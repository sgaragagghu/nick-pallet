// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Nicks Module
//!
//! - [`nicks::Config`](./trait.Config.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! Nicks is an example module for keeping track of account names on-chain. It makes no effort to
//! create a name hierarchy, be a DNS replacement or provide reverse lookups. Furthermore, the
//! weights attached to this module's dispatchable functions are for demonstration purposes only and
//! have not been designed to be economically secure. Do not use this pallet as-is in production.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! * `set_name` - Set the associated name of an account; a small deposit is reserved if not already
//!   taken.
//! * `clear_name` - Remove an account's associated name; the deposit is returned.
//! * `kill_name` - Forcibly remove the associated name; the deposit is lost.
//!
//! [`Call`]: ./enum.Call.html
//! [`Config`]: ./trait.Config.html

#![cfg_attr(not(feature = "std"), no_std)]
// something like a macro, the ! means it will apply to this file. Otherwise it will apply to the following block.
//cfg_attr means that if the first `object` -in this case it is not(feature = `std`)- is true then it will expand to
//#![no_std]
//cfg_attr can have more things after the second `object`... with commas. It will just exand each of it.. fir example
//#![A]
//#![B]
//#![C]
//etc
//cfg_attr can even be concatenated with another cfg_attr
//So basically if the std feature is not `enabled` -> not(false) -> true so it exands to no_std
//std means it will be linked to kinda the `standard library`, otherwise it will be linked to an alternative library which is the core rust library.
//std is used in normal compilation but when it is used runtime std library is not available and thus it will be compiled with no_std.
//some functions are not available or different between std and no_std, it means we must be sure it will work in both ways -std and no_std-

//Example of use: it bsically bind the final object to the complete path(object included)
// use path::to::object
// now we can locally write object instead of path::to::object
/*
use crate::deeply::nested::{
    my_first_function,
    my_second_function,
    AndATraitType
};

fn main() {
    my_first_function();
}
*/

use sp_std::prelude::*; // binding all the objects in that path
use sp_runtime::{
	traits::{StaticLookup, Zero} //eventualy binding these two objects
};
use frame_support::{ //just binding
	decl_module, decl_event, decl_storage, ensure, decl_error,
	traits::{Currency, EnsureOrigin, ReservableCurrency, OnUnbalanced, Get},
};
use frame_system::ensure_signed; //just binding

// THE FOLLOWING EXPLANATION MAY CONTAIN ERROR SINCE IT'S DIFFICULT TO UNDERSTAND AND NEEDS INFORMATIONS I'LL GET GOING AHEAD READING AND COMMENTING
// type will create a type ALIAS (NOT A NEW TYPE!)
// the grammar of 'as' looks something like: expression 'as' type
// So T as Config is kinda a cast so T must implement that trait - so it is a trait constrain..
// A: <T as Config>::Currency should refer to associated type Currency in the impementation of a trait Config for a type T.
// B: <T as frame_system::Config>::AccountId should refer to associated type AccountId int the implementation of a trait Config (in frame_system) for a type T.
// <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance combination of the two, should refer to associated type 
// Balance in the implementation of a trait B for a type A.
type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance; //alias
type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::NegativeImbalance; //alias

//pub means it is vicible outside of this crate. Otherwise it would be private, if private it is only visible by this crate and its descendants
//trait defiinition: it is something like a java class definition - then each data type can implement it and be treated as they are the same `object` 
//even if data types are different. 
//trait can define functions and methods, types, constants.
//this part `: frame_system::Config` means that this is a subtrait of : frame_system::Config (also you can call it supertrait)
//just a specialization of the trait.
pub trait Config: frame_system::Config {
// Self refers to current type that implements the trait
// Trait bounds, exampple: `type OneType: TwoTrait + ThreeTrait` means that the OneType *associated* type must implement both TwoTrait and ThreeTrait traits

// So the Event associated type must implement std::convert::From and std::convert::Into which are
// both traits used to do value-to-value conversions while consuming the input value (Into is somehow the 'fallback' of From)
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>; // trait bound

// the Currency associated type must implement the trait frame_support::traits::ReservableCurrency
// A currency where funds can be reserved from the user.
// PROBABLY IT MEANS WE HAVE TO IMPEMENT SOMETHING? LET'S SEE
	/// The currency trait.
	type Currency: ReservableCurrency<Self::AccountId>; // trait bound

//ALPHA
// the ReservationFee associated type must implement the trait frame_support::traits::Get
// A trait for querying a single value from a type.
// It is not required that the value is constant.
// So afaiu it means ReservationFee must implements a get function
	/// Reservation fee.
	type ReservationFee: Get<BalanceOf<Self>>; // trait bound

// the Slashed associated type must implement the trait frame_support::traits::OnUnbalanced
// Handler for when some currency "account" decreased in balance for some reason.
	/// What to do with slashed funds.
	type Slashed: OnUnbalanced<NegativeImbalanceOf<Self>>; // trait bound

// the ForceOrigin associated type must implement the trait frame_support::traits::EnsureOrigin
// Some sort of check on the origin is performed by this object.
	/// The origin which may forcibly set or remove a name. Root can always do this.
	type ForceOrigin: EnsureOrigin<Self::Origin>; // trait bound
//Same as ALPHA
	/// The minimum length a name may be.
	type MinLength: Get<usize>; // trait bound
//Same as ALPHA
	/// The maximum length a name may be.
	type MaxLength: Get<usize>; // trait bound
}

// the visibility of Substrate storage items only impacts whether or not other pallets within the runtime will be able to access a storage item.
decl_storage! { // macro!, macro is a macro because there is the ! - https://substrate.dev/docs/en/knowledgebase/runtime/storage
// FOR keyword in this context shoud create an implementation (but in this case it should be impl and not trait...)
// a concrete type that implements the trait store ... PROBABLY IS JUST MEANS we are implementing 
// the type in this case is Module<T: Config> as Nicks which means 
// Module<T: Config> casted as Nicks
// <T: Config> .. : Config is a trait constraint that means the type which Module will take must implement that Config trait...
	//here store items
	trait Store for Module<T: Config> as Nicks {
// Type Option represents an optional value: every Option is either Some and contains a value, or None, and does not.
// It seems here NameOf is declared as something like a function?
// it should somehow create hash from the key which is AccountId (it should be a type) and the `payload` should be the
// tuple Vec<u8>, BalanceOf<T>)> (which are both types, well the latter is an alias.)
// Vec<u8> is pobably a vector of u8 which (should be chars... not true lol)
		/// The lookup table for names.
		NameOf: map hasher(twox_64_concat) T::AccountId => Option<(Vec<u8>, BalanceOf<T>)>;
	}
}

// To declare an event, use the decl_event! macro. Like any rust enum, Events have names and can optionally carry data with them. 
// The syntax is slightly different depending on whether the events carry data of primitive types, or generic types from the pallet's configuration trait.
// Having a transaction included in a block does not guarantee that the function executed successfully.
// To verify that functions have executed successfully, emit an event at the bottom of the function body.
// Events notify the off-chain world of successful state transitions.
// https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html
// enum create just something like a SYMBOL, normally... like
/*
enum IpAddrKind {
    V4,
    V6,
}
    let four = IpAddrKind::V4;
    let six = IpAddrKind::V6;
IpAddrKind is the type
now a function eg. called route that can take just IpAddrKind... obviously
And we can call this function with either variant:

    route(IpAddrKind::V4);
    route(IpAddrKind::V6);
then we can attach some variable to wach enum kind like... 
enum IpAddrKind {
    V4(String),
    V6(String),
}
instead 
enum IpAddrKind<T> {
    V4(T),
    V6(T),
}
means we an call it with whatever data type
*/

decl_event!( // https://substrate.dev/recipes/events.html
//this T instead id needed for the trait bound <T as frame_system::Config>::AccountId
// so basically means T must implement the trait frame_system::Config
	pub enum Event<T> where AccountId = <T as frame_system::Config>::AccountId, Balance = BalanceOf<T> { // where clause can be used to specify type aliasing for more readable code.
// list of the events

		/// A name was set. \[who\]
		NameSet(AccountId),
		/// A name was forcibly set. \[target\]
		NameForced(AccountId),
		/// A name was changed. \[who\]
		NameChanged(AccountId),
		/// A name was cleared, and the given balance returned. \[who, deposit\]
		NameCleared(AccountId, Balance),
		/// A name was removed and the given balance slashed. \[target, deposit\]
		NameKilled(AccountId, Balance),
	}
);

// To define error types which a pallet may return in its dispatchable functions. Dispatchable functions return 
// DispatchResult, with either an Ok(()), or DispatchError containing custom errors defined in this macro.

// So FOR is used to implement a trait into a type basically
// so Error is implementing the Module trait

decl_error! {
	/// Error for the nicks module.
	pub enum Error for Module<T: Config> { // : Config type constraint
		/// A name is too short.
		TooShort,
		/// A name is too long.
		TooLong,
		/// An account isn't named.
		Unnamed,
	}
}

// https://substrate.dev/docs/en/knowledgebase/runtime/macros#decl_module
// To define dispatchable functions in a pallet
// The macro declares a Module struct and Call enum type for the containing pallet. 
// It combines the necessary logics using user-defined dispatchable calls into the two types (modules and types).

decl_module! {
	/// Nicks module declaration.
	pub struct Module<T: Config> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Reservation fee.
		const ReservationFee: BalanceOf<T> = T::ReservationFee::get();

		/// The minimum length a name may be.
		const MinLength: u32 = T::MinLength::get() as u32;

		/// The maximum length a name may be.
		const MaxLength: u32 = T::MaxLength::get() as u32;

		/// Set an account's name. The name should be a UTF-8-encoded string by convention, though
		/// we don't check it.
		///
		/// The name may not be more than `T::MaxLength` bytes, nor less than `T::MinLength` bytes.
		///
		/// If the account doesn't already have a name, then a fee of `ReservationFee` is reserved
		/// in the account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - At most one balance operation.
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[weight = 50_000_000]
		fn set_name(origin, name: Vec<u8>) {
			let sender = ensure_signed(origin)?;

			ensure!(name.len() >= T::MinLength::get(), Error::<T>::TooShort);
			ensure!(name.len() <= T::MaxLength::get(), Error::<T>::TooLong);

			let deposit = if let Some((_, deposit)) = <NameOf<T>>::get(&sender) {
				Self::deposit_event(RawEvent::NameChanged(sender.clone()));
				deposit
			} else {
				let deposit = T::ReservationFee::get();
				T::Currency::reserve(&sender, deposit.clone())?;
				Self::deposit_event(RawEvent::NameSet(sender.clone()));
				deposit
			};

			<NameOf<T>>::insert(&sender, (name, deposit));
		}

		/// Clear an account's name and return the deposit. Fails if the account was not named.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - One balance operation.
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[weight = 70_000_000]
		fn clear_name(origin) {
			let sender = ensure_signed(origin)?;

			let deposit = <NameOf<T>>::take(&sender).ok_or(Error::<T>::Unnamed)?.1;

			let _ = T::Currency::unreserve(&sender, deposit.clone());

			Self::deposit_event(RawEvent::NameCleared(sender, deposit));
		}

		/// Remove an account's name and take charge of the deposit.
		///
		/// Fails if `who` has not been named. The deposit is dealt with through `T::Slashed`
		/// imbalance handler.
		///
		/// The dispatch origin for this call must match `T::ForceOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// - One unbalanced handler (probably a balance transfer)
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[weight = 70_000_000]
		fn kill_name(origin, target: <T::Lookup as StaticLookup>::Source) {
			T::ForceOrigin::ensure_origin(origin)?;

			// Figure out who we're meant to be clearing.
			let target = T::Lookup::lookup(target)?;
			// Grab their deposit (and check that they have one).
			let deposit = <NameOf<T>>::take(&target).ok_or(Error::<T>::Unnamed)?.1;
			// Slash their deposit from them.
			T::Slashed::on_unbalanced(T::Currency::slash_reserved(&target, deposit.clone()).0);

			Self::deposit_event(RawEvent::NameKilled(target, deposit));
		}

		/// Set a third-party account's name with no deposit.
		///
		/// No length checking is done on the name.
		///
		/// The dispatch origin for this call must match `T::ForceOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// - At most one balance operation.
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[weight = 70_000_000]
		fn force_name(origin, target: <T::Lookup as StaticLookup>::Source, name: Vec<u8>) {
			T::ForceOrigin::ensure_origin(origin)?;

			let target = T::Lookup::lookup(target)?;
			let deposit = <NameOf<T>>::get(&target).map(|x| x.1).unwrap_or_else(Zero::zero);
			<NameOf<T>>::insert(&target, (name, deposit));

			Self::deposit_event(RawEvent::NameForced(target));
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{
		assert_ok, assert_noop, impl_outer_origin, parameter_types,
		ord_parameter_types
	};
	use sp_core::H256;
	use frame_system::EnsureSignedBy;
	use sp_runtime::{
		testing::Header, traits::{BlakeTwo256, IdentityLookup, BadOrigin},
	};

	impl_outer_origin! {
		pub enum Origin for Test where system = frame_system {}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub BlockWeights: frame_system::limits::BlockWeights =
			frame_system::limits::BlockWeights::simple_max(1024);
	}
	impl frame_system::Config for Test {
		type BaseCallFilter = ();
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = ();
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type Version = ();
		type PalletInfo = ();
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
	}
	impl pallet_balances::Config for Test {
		type MaxLocks = ();
		type Balance = u64;
		type Event = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type WeightInfo = ();
	}
	parameter_types! {
		pub const ReservationFee: u64 = 2;
		pub const MinLength: usize = 3;
		pub const MaxLength: usize = 16;
	}
	ord_parameter_types! {
		pub const One: u64 = 1;
	}
	impl Config for Test {
		type Event = ();
		type Currency = Balances;
		type ReservationFee = ReservationFee;
		type Slashed = ();
		type ForceOrigin = EnsureSignedBy<One, u64>;
		type MinLength = MinLength;
		type MaxLength = MaxLength;
	}
	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type Nicks = Module<Test>;

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![
				(1, 10),
				(2, 10),
			],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn kill_name_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Nicks::set_name(Origin::signed(2), b"Dave".to_vec()));
			assert_eq!(Balances::total_balance(&2), 10);
			assert_ok!(Nicks::kill_name(Origin::signed(1), 2));
			assert_eq!(Balances::total_balance(&2), 8);
			assert_eq!(<NameOf<Test>>::get(2), None);
		});
	}

	#[test]
	fn force_name_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				Nicks::set_name(Origin::signed(2), b"Dr. David Brubeck, III".to_vec()),
				Error::<Test>::TooLong,
			);

			assert_ok!(Nicks::set_name(Origin::signed(2), b"Dave".to_vec()));
			assert_eq!(Balances::reserved_balance(2), 2);
			assert_ok!(Nicks::force_name(Origin::signed(1), 2, b"Dr. David Brubeck, III".to_vec()));
			assert_eq!(Balances::reserved_balance(2), 2);
			assert_eq!(<NameOf<Test>>::get(2).unwrap(), (b"Dr. David Brubeck, III".to_vec(), 2));
		});
	}

	#[test]
	fn normal_operation_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Nicks::set_name(Origin::signed(1), b"Gav".to_vec()));
			assert_eq!(Balances::reserved_balance(1), 2);
			assert_eq!(Balances::free_balance(1), 8);
			assert_eq!(<NameOf<Test>>::get(1).unwrap().0, b"Gav".to_vec());

			assert_ok!(Nicks::set_name(Origin::signed(1), b"Gavin".to_vec()));
			assert_eq!(Balances::reserved_balance(1), 2);
			assert_eq!(Balances::free_balance(1), 8);
			assert_eq!(<NameOf<Test>>::get(1).unwrap().0, b"Gavin".to_vec());

			assert_ok!(Nicks::clear_name(Origin::signed(1)));
			assert_eq!(Balances::reserved_balance(1), 0);
			assert_eq!(Balances::free_balance(1), 10);
		});
	}

	#[test]
	fn error_catching_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(Nicks::clear_name(Origin::signed(1)), Error::<Test>::Unnamed);

			assert_noop!(
				Nicks::set_name(Origin::signed(3), b"Dave".to_vec()),
				pallet_balances::Error::<Test, _>::InsufficientBalance
			);

			assert_noop!(Nicks::set_name(Origin::signed(1), b"Ga".to_vec()), Error::<Test>::TooShort);
			assert_noop!(
				Nicks::set_name(Origin::signed(1), b"Gavin James Wood, Esquire".to_vec()),
				Error::<Test>::TooLong
			);
			assert_ok!(Nicks::set_name(Origin::signed(1), b"Dave".to_vec()));
			assert_noop!(Nicks::kill_name(Origin::signed(2), 1), BadOrigin);
			assert_noop!(Nicks::force_name(Origin::signed(2), 1, b"Whatever".to_vec()), BadOrigin);
		});
	}
}
