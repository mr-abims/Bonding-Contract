// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;
interface ITreasury {
    function deposit(address _principleTokenAddress, uint _amountPrincipleToken, uint _amountPayoutToken) external;
    function valueOfToken( address _principleTokenAddress, uint _amount ) external view returns ( uint value_ );
}
