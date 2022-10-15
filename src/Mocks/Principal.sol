pragma solidity ^0.8.0;

import "../../lib/openzeppelin-contracts/contracts/token/ERC20/ERC20.sol";

contract Principal is ERC20("principal", "PAL") {
    constructor() public {
        _mint(msg.sender, 1000000e18);
    
    }

}
