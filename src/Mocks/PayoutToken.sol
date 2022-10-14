pragma solidity ^0.7.5;

import "../../lib/openzeppelin-contracts/contracts/token/ERC20/ERC20.sol";

contract MOCKWAKANDA is ERC20("Payout", "POT") {
    constructor() public {
        _mint(msg.sender, 1000000e9);
    
    }
    function mintToUser() public {
        _mint(msg.sender, 1000000e9);
    }
}
