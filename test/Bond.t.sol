// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.7.5;

import "forge-std/Test.sol";
import "../src/CustomBond.sol";

contract CounterTest is Test {
  CustomBond public bond;

    function setUp() public {
        bond = new CustomBond();
    }

   
}

