****************************************************************************************************************************************************
*                                                               MARKET CLEARING MODEL                                                              *
*************************************************************************************************-Developed by Joao Augusto Silva Ledo-*************
* This code encompasses covers a simple market clearing model coded in GAMS with focus on its coding strucutres such as its SETS and connections   *
****************************************************************************************************************************************************

Sets
    I Producer /I1, I2/
    J Consumers /J1/
    U Producers' Units /U1, U2/
    C Consumers' Demands /C1/
    UnitGeneratorConect(I, U) Connection between Producers and its units /I1.U1, I2.U2/
    UnitConsumerConect(J, C) Connection between Consumers and its demands /J1.C1/;
    
Parameters
    cost(i, u) Producers' Costs /I1.U1 = 1, I2.U2 = 2/
    max_utility(j, c) Consumers'maximum Utilities /J1.C1 = 3/
    p_max(i, u) Producers' maximum power generation /I1.U1 = 6, I2.U2 = 6/
    d_max(j, c) Consumer's maximum power demand /J1.C1 = 10/
    
    profit(i)
    utility(j)
    Cleared_Price
    o(i, u) Producers' Offers 
    b(j, c) Consumers' Bids;
    
Variables
    p(i, u) Power produced
    d(j, c) Power consumed;

Free Variable
    Social_Welfare Social welfare objective function variable;

Equations
    Objective_Function
    balance
    producer_upperboundary(i, u)
    producer_lowerboundary(i, u)
    consumer_upperboundary(j, c)
    consumer_lowerboundary(j, c);

* PRE EXECUTE *
* Perfect Competition *
o(i, u) = cost(i, u);
b(j, c) = max_utility(j, c);
    
*MARKET CLEARING MODEL*

* Objective Function
Objective_Function.. Social_Welfare =e= sum(j, sum(c $ UnitConsumerConect(j, c), b(j, c)*d(j, c))) - sum(i, sum(u $ UnitGeneratorConect(i, u), o(i, u)*p(i, u)));

* Constraints *

* Balance
balance.. sum(i, sum(u $ UnitGeneratorConect(i, u), p(i, u))) - sum(j, sum(c $ UnitConsumerConect(j, c), d(j, c))) =e= 0;
* Upper bound power dispatched
producer_lowerboundary(i, u) $ UnitGeneratorConect(i, u).. p(i, u) =g= 0;
* Lower bound power disptached
producer_upperboundary(i, u) $ UnitGeneratorConect(i, u).. p(i, u) =l= p_max(i, u);
* Upper bound power demanded
consumer_lowerboundary(j, c) $ UnitConsumerConect(j, c).. d(j, c) =g= 0;
* Lower bound power demanded
consumer_upperboundary(j, c) $ UnitConsumerConect(j, c).. d(j, c) =l= d_max(j, c);

*Model Market_Clearing /Objective_Function, balance, producer_upperboundary, producer_lowerboundary
*consumer_upperboundary, consumer_lowerboundary/;

Model Market_Clearing /all/;
option MIP = CPLEX;
solve Market_Clearing maximizing Social_Welfare using MIP;

* POST EXECUTE *
Cleared_Price = abs(balance.m);
profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);

display o;
display b;
display Cleared_Price;
display profit;
display utility;
