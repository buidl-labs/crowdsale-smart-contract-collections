pragma solidity ^0.5.2;

import "./MyTokenERC20Mintable.sol"; 
import 'openzeppelin-solidity/contracts/crowdsale/Crowdsale.sol';
import 'openzeppelin-solidity/contracts/crowdsale/emission/MintedCrowdsale.sol';

contract MyCrowdsale is Crowdsale, MintedCrowdsale {
    constructor(
        uint256 _rate,    // rate in TKNbits
        address payable _wallet,
        ERC20 _token
    )
        MintedCrowdsale()
        Crowdsale(_rate, _wallet, _token)
        public
    {

    }
}