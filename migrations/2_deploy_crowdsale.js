const TF_ERC_20 = artifacts.require("./TF_ERC_20.sol");
const TF_ERC_20_CrowdSale = artifacts.require("./TF_ERC_20_CrowdSale.sol");

const ether = n => new web3.BigNumber();

const duration = {
  seconds: function(val) {
    return val;
  },
  minutes: function(val) {
    return val * this.seconds(60);
  },
  hours: function(val) {
    return val * this.minutes(60);
  },
  days: function(val) {
    return val * this.hours(24);
  },
  weeks: function(val) {
    return val * this.days(7);
  },
  years: function(val) {
    return val * this.days(365);
  }
};

module.exports = async function(deployer, network, accounts) {
  const _name = "TECHFUND Token";
  const _symbol = "TF";
  const _decimals = 18;

  await deployer.deploy(TF_ERC_20, _name, _symbol, _decimals);
  const deployedToken = await TF_ERC_20.deployed();

  const latestTime = new Date().getTime();

  const _rate = 500;
  const _wallet = accounts[0];
  const _token = deployedToken.address;
  const _openingTime = latestTime + duration.minutes(1);
  const _closingTime = _openingTime + duration.weeks(1);
  const _cap = web3.utils.toWei("100", "ether");
  const _goal = web3.utils.toWei("50", "ether");
  const _foundersFund = accounts[1];
  const _foundationFund = accounts[2];
  const _partnersFund = accounts[3];
  const _releaseTime = _closingTime + duration.days(1);

  await deployer.deploy(
    TF_ERC_20_CrowdSale,
    _rate,
    _wallet,
    _token,
    _cap,
    _openingTime,
    _closingTime,
    _goal,
    _foundersFund,
    _foundationFund,
    _partnersFund,
    _releaseTime
  );

  return true;
};
