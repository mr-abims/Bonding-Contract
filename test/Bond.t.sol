// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../src/Mocks/payout.sol";
import "../src/Mocks/Principal.sol";
import "../src/Bond.sol";

contract BondTest is Test {
  Bond public bond;
  PAYOUT public payout;
  Principal public principal;
  address treasury = 0xeA0D961D4D1312876C25b31F8383676e71D2E98C;


function setUp() public {
    bond = new Bond(
        treasury, 
        address(payout), 
        address(principal)
        
        );

    payout = new PAYOUT();
    principal = new Principal();
}


    
function mkaddr(string memory name) public returns (address) {
        address addr = address(
            uint160(uint256(keccak256(abi.encodePacked(name))))
        );
        vm.label(addr, name);
        return addr;
    }
   

}
