const crowdsaleobject = {
  crowdsaledetail: [
    {
      name: "MintedCrowdsale",
      path:
        "./openzeppelin-solidity/contracts/crowdsale/emission/MintedCrowdsale.sol",
      constructor: [],
      arguments: []
    },
    {
      name: "AllowanceCrowdsale",
      path:
        "./openzeppelin-solidity/contracts/crowdsale/emission/AllowanceCrowdsale.sol",
      constructor: ["address tokenWallet"],
      arguments: ["AllowanceCrowdsale(tokenWallet)"]
    },
    {
      name: "PostDeliveryCrowdsale",
      path:
        "./openzeppelin-solidity/contracts/crowdsale/distribution/PostDeliveryCrowdsale.sol",
      constructor: ["uint256 openingTime", "uint256 closingTime"],
      arguments: ["TimedCrowdsale(openingTime,closingTime)"]
    },
    {
      name: "RefundableCrowdsale",
      path:
        "./openzeppelin-solidity/contracts/crowdsale/distribution/RefundableCrowdsale.sol",
      constructor: [
        "uint256 goal",
        "uint256 openingTime",
        "uint256 closingTime"
      ],
      arguments: [
        "RefundableCrowdsale(goal)",
        "TimedCrowdsale(openingTime,closingTime)"
      ]
    },
    {
      name: "TimedCrowdsale",
      path:
        "./openzeppelin-solidity/contracts/crowdsale/validation/TimedCrowdsale.sol",
      constructor: ["uint256 openingTime", "uint256 closingTime"],
      arguments: ["TimedCrowdsale(openingTime,closingTime)"]
    },
    {
      name: "CappedCrowdsale",
      path:
        "./openzeppelin-solidity/contracts/crowdsale/validation/CappedCrowdsale.sol",
      constructor: ["uint256 _cap"],
      arguments: ["CappedCrowdsale(_cap)"]
    },
    {
      name: "IndividuallyCappedCrowdsale",
      path:
        "./openzeppelin-solidity/contracts/crowdsale/validation/IndividuallyCappedCrowdsale.sol",
      constructor: [],
      arguments: []
    },
    {
      name: "WhitelistCrowdsale",
      path:
        "./openzeppelin-solidity/contracts/crowdsale/validation/WhitelistCrowdsale.sol",
      constructor: [],
      arguments: []
    },
    {
      name: "IncreasingPriceCrowdsale",
      path:
        "./openzeppelin-solidity/contracts/crowdsale/price/IncreasingPriceCrowdsale.sol",
      constructor: ["uint256 initialRate", "uint256 finalRate"],
      arguments: ["IncreasingPriceCrowdsale(initialRate,finalRate)"]
    }
  ]
};
