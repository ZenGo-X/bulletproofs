/*

Copyright 2018 by Kzen Networks

This file is part of bulletproof library
(https://github.com/KZen-networks/bulletproof)

bulletproof is free software: you can redistribute
it and/or modify it under the terms of the GNU General Public
License as published by the Free Software Foundation, either
version 3 of the License, or (at your option) any later version.

@license GPL-3.0+ <https://github.com/KZen-networks/bulletproof/blob/master/LICENSE>
*/

#![allow(clippy::many_single_char_names, clippy::too_many_arguments)]

// based on the paper: https://eprint.iacr.org/2017/1066.pdf
#[macro_use]
extern crate serde_derive;
extern crate serde;

extern crate curv;
extern crate generic_array;
extern crate itertools;
extern crate sha2;

pub mod proofs;

#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum Errors {
    InnerProductError,
    WeightedInnerProdError,
    RangeProofError,
}
