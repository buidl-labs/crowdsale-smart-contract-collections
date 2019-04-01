pragma solidity ^0.5.2;

import 'openzeppelin-solidity/contracts/token/ERC20/ERC20.sol';
import 'openzeppelin-solidity/contracts/token/ERC20/ERC20Mintable.sol';


contract MyToken is ERC20,  ERC20Mintable {
	string public name = "SimpleToken";
	string public symbol = "SPT";
	uint8 public decimals = 18;


    constructor(
        string memory _name,
        string memory _symbol,
        uint8 _decimals
    )
        ERC20Mintable()
        ERC20()
        public
    {
		name = _name;
		symbol = _symbol;
		decimals = _decimals;
	}
}