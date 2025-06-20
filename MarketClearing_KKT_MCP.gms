***************************************************************************
*                        KKT MARKET CLEARING (MCP)                        *
***************************************************************************


***************************************************************************
* SETS
***************************************************************************
Sets
    I Producer /I1, I2/
    J Consumers /J1/
    U Producers' Units /U1, U2/
    C Consumers' Demands /C1/
    UnitGeneratorConect(I, U) Connection between Producers and its units /I1.U1, I2.U2/
    UnitConsumerConect(J, C) Connection between Consumers and its demands /J1.C1/;
    

***************************************************************************
* DATA
***************************************************************************
Parameters
    cost(i, u) Producers' Costs /I1.U1 = 1, I2.U2 = 2/
    max_utility(j, c) Consumers'maximum Utilities /J1.C1 = 3/
    p_max(i, u) Producers' maximum power generation /I1.U1 = 6, I2.U2 = 6/
    d_max(j, c) Consumer's maximum power demand /J1.C1 = 10/
    
    Social_Welfare
    profit(i)
    utility(j)
    Cleared_Price
    o(i, u) Producers' Offers 
    b(j, c) Consumers' Bids;
    

***************************************************************************
* CREATING VARIABLES
***************************************************************************

Variables
    p(i, u) Power produced
    d(j, c) Power consumed;
    lambda Cleared Price;
    
Positive Variables
    mu_p_min(i, u) dual variable associated to variable p lower bound constraint
    mu_p_max(i, u) dual variable associated to variable p upper bound constraint
    mu_d_min(j, c) dual variable associated to variable d lower bound constraint
    mu_d_max(j, c) dual variable associated to variable d upper bound constraint;

Free Variable
     OF Social welfare objective function variable;


***************************************************************************
* EQUATIONS
***************************************************************************

Equations
    Objective_Function
    balance
    producer_upperboundary(i, u)
    producer_lowerboundary(i, u)
    consumer_upperboundary(j, c)
    consumer_lowerboundary(j, c)
    Deriv_p(i, u)
    Deriv_d(j, c)
    comp_p_min(i, u)
    comp_p_max(i, u)
    comp_d_min(j, c)
    comp_d_max(j, c)
    Dual_Positivity_mu_p_max(i, u)
    Dual_Positivity_mu_d_max(j, c)
    Dual_Positivity_mu_p_min(i, u)
    Dual_Positivity_mu_d_min(j, c);

***************************************************************************
* PRE EXECUTE
***************************************************************************

* Perfect Competition *
o(i, u) = cost(i, u);
b(j, c) = max_utility(j, c);

*    p.l(i, u) = p_max(i, u);
*    d.l(j, c) = d_max(j, c);

    
***************************************************************************
* MODEL
***************************************************************************

* Objective function
Objective_Function.. OF =e= 1;

* Constraints *

*Primal Constraints
* Power balance supply
balance.. sum(i, sum(u $ UnitGeneratorConect(i, u), p(i, u))) - sum(j, sum(c $ UnitConsumerConect(j, c), d(j, c))) =e= 0;
* Upper bound power dispatched
producer_lowerboundary(i, u) $ UnitGeneratorConect(i, u).. p(i, u) =g= 0;
* Lower bound power disptached
producer_upperboundary(i, u) $ UnitGeneratorConect(i, u).. - p(i, u) + p_max(i, u) =g= 0;
* Upper bound power demanded
consumer_lowerboundary(j, c) $ UnitConsumerConect(j, c).. d(j, c) =g= 0;
* Lower bound power demanded
consumer_upperboundary(j, c) $ UnitConsumerConect(j, c).. -d(j, c) + d_max(j, c) =g= 0;

*Partial derivatives (gradient)
Deriv_p(i, u) $ UnitGeneratorConect(i, u).. o(i, u) - lambda - mu_p_min(i, u) + mu_p_max(i, u) =e= 0;
Deriv_d(j, c) $ UnitConsumerConect(j, c).. -b(j, c) + lambda - mu_d_min(j, c) + mu_d_max(j, c) =e= 0;

*Complementarities
comp_p_min(i, u) $ UnitGeneratorConect(i, u).. p(i, u)*mu_p_min(i, u) =e= 0;
comp_p_max(i, u) $ UnitGeneratorConect(i, u).. (p_max(i, u)- p(i, u))*mu_p_max(i, u) =e= 0;
comp_d_min(j, c) $ UnitConsumerConect(j, c).. d(j, c)*mu_d_min(j, c) =e= 0;
comp_d_max(j, c) $ UnitConsumerConect(j, c).. (d_max(j, c) - d(j, c))*mu_d_max(j, c) =e= 0;

*Dual variables positivity
    
Dual_Positivity_mu_p_min(i, u) $ UnitGeneratorConect(i, u).. mu_p_min(i, u) =g= 0;
Dual_Positivity_mu_p_max(i, u) $ UnitGeneratorConect(i, u).. mu_p_max(i, u) =g= 0;
Dual_Positivity_mu_d_min(j, c) $ UnitConsumerConect(j, c).. mu_d_min(j, c) =g= 0;
Dual_Positivity_mu_d_max(j, c) $ UnitConsumerConect(j, c).. mu_d_max(j, c) =g= 0;

******************************************************************************************
* SOLVING THE MCP AS AN OPTIMIZATION MODEL USING AN UNITARY AUXILIARY OBJECTIVE FUNCTION *
******************************************************************************************

*Model Market_Clearing /Objective_Function, balance, producer_upperboundary, producer_lowerboundary
*consumer_upperboundary, consumer_lowerboundary/;

Model KKT_Market_Clearing_OF /all/;
option MIP = CPLEX;
option NLP = KNITRO;
solve KKT_Market_Clearing_OF maximizing OF using NLP;

* POST EXECUTE *
Cleared_Price = lambda.l;
profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
Social_Welfare = sum(j, sum(c $ UnitConsumerConect(j, c), b(j, c)*d.l(j, c))) - sum(i, sum(u $ UnitGeneratorConect(i, u), o(i, u)*p.l(i, u)))
display o;
display b;
display Cleared_Price;
display Social_Welfare;
display profit;
display utility;

******************************************************************************************

******************************************************************************************
* SOLVING THE MCP AS A MCP THROUGH SOLVER PATH *
******************************************************************************************
Model KKT_Market_Clearing_MCP /balance.lambda, producer_lowerboundary.mu_p_min, producer_upperboundary.mu_p_max, 
consumer_lowerboundary.mu_d_min, consumer_upperboundary.mu_d_max, Deriv_p.p, Deriv_d.d/;

option MCP = PATH;

solve KKT_Market_Clearing_MCP using MCP;
* POST EXECUTE *
Cleared_Price = lambda.l;
profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
Social_Welfare = sum(j, sum(c $ UnitConsumerConect(j, c), b(j, c)*d.l(j, c))) - sum(i, sum(u $ UnitGeneratorConect(i, u), o(i, u)*p.l(i, u)))
display o;
display b;
display Cleared_Price;
display Social_Welfare;
display profit;
display utility;
******************************************************************************************