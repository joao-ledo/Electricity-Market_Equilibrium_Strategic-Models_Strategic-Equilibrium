****************************************************************************************************************************************************
*                                                     MARKET CLEARING IN AN EQUILIBRIUM STRUCTURE                                                  *
*************************************************************************************************-Developed by Joao Augusto Silva Ledo-*************
* This code covers an equilibrium model perspective of a market clearing with perfect competition, having 3 models in equilibrium solved by EMP:   *
* 1. A producer concerning to maximize its onw profit                                                                                              *
* 2. A producer concernign to maximize its onw utility                                                                                             *
* 3. An agent accountable to secure the power balance supply between producers and consumers and provide the cleared price                         *
****************************************************************************************************************************************************

Sets
    I All Producers /I1, I2/
    U All Producers' Units /U1, U2/
    J All Consumers /J1/
    C All Consumers' Units /C1/
    UnitGeneratorConect(I, U) /I1.U1, I2.U2/
    UnitConsumerConect(J, C) /J1.C1/;
    
Parameters
    cost(i, u) /I1.U1 = 1, I2.U2 = 2/
    utility(j, c) /J1.C1 = 3/
    p_max(i, u) /I1.U1 = 6, I2.U2 = 6/
    d_max(j, c) /J1.C1 = 10/
    Social_Welfare    
    Cleared_Price
    o(i, u) Producers' Offers 
    b(j, c) Consumers' Bids;
    
Variables
    p(i, u) Power produced
    d(j, c) Power consumed
    lambda Cleared price;

Free Variable
     Profit(i)
     Utility(j)
     OF;

Equations
    Objective_Function_Profit(i)
    Objective_Function_Utility(j)
    Objective_Function_OF
    balance
    producer_upperboundary(i, u)
    producer_lowerboundary(i, u)
    consumer_upperboundary(j, c)
    consumer_lowerboundary(j, c);

* PRE EXECUTE *
* Perfect Competition *
o(i, u) = cost(i, u);
b(j, c) = max_utility(j, c);
    
* MARKET CLEARING EQUILIBRIUM MODEL*

* OBJECTIVE FUNCTION
    Objective_Function_Profit(i).. Profit(i) =e= sum(u $ UnitGeneratorConect(i, u), lambda*p(i, u) - p(i, u)*o(i, u));
    Objective_Function_Utility(j).. Utility(j) =e= sum(c $ UnitConsumerConect(j, c), b(j, c)*d(j, c) - lambda*d(j, c));
    Objective_Function_OF.. OF =e= 1;

* CONSTRAINTS *
* Power balance supply
balance.. sum(i, sum(u $ UnitGeneratorConect(i, u), p(i, u))) - sum(j, sum(c $ UnitConsumerConect(j, c), d(j, c))) =e= 0;
* Upper bound power dispatched
producer_lowerboundary(i, u) $ UnitGeneratorConect(i, u).. p(i, u) =g= 0;
* Lower bound power disptached
producer_upperboundary(i, u) $ UnitGeneratorConect(i, u).. p(i, u) =l= p_max(i, u);
* Upper bound power demanded
consumer_lowerboundary(j, c) $ UnitConsumerConect(j, c).. d(j, c) =g= 0;
* Lower bound power demanded
consumer_upperboundary(j, c) $ UnitConsumerConect(j, c).. d(j, c) =l= d_max(j, c);


Model EquilibriumMarketClearAgents /Objective_Function_Profit, Objective_Function_Utility, Objective_Function_OF,
balance, producer_lowerboundary, producer_upperboundary, consumer_lowerboundary, consumer_upperboundary/;

*Model EquilibriumMarketClearAgents /all/;

$onecho > empinfo.txt
equilibrium
max Profit(i)              s.t. p(i, u)$ UnitGeneratorConect(i, u), Objective_Function_Profit(i), producer_lowerboundary(i, u)$ UnitGeneratorConect(i, u), producer_upperboundary(i, u)$ UnitGeneratorConect(i, u)
max Utility(j)             s.t. d(j, c)$ UnitConsumerConect(j, c), Objective_Function_Utility(j), consumer_lowerboundary(j, c) $ UnitConsumerConect(j, c), consumer_upperboundary(j, c) $ UnitConsumerConect(j, c)
max OF                     s.t.                                                                   Objective_Function_OF, balance
dualvar lambda, balance
$offecho

$libinclude empmodel empinfo.txt
$echo SharedEqu > jams.opt
EquilibriumMarketClearAgents.optfile = 1;

***************************************************************************
* SOLVING
***************************************************************************
solve EquilibriumMarketClearAgents using emp;

* POST EXECUTE *
Cleared_Price = lambda.l;
Social_Welfare = sum(j, sum(c $ UnitConsumerConect(j, c), b(j, c)*d.l(j, c))) - sum(i, sum(u $ UnitGeneratorConect(i, u), o(i, u)*p.l(i, u)))
display o;
display b;
display Cleared_Price;
display Social_Welfare;
display Profit.l;
display Utility.l;
