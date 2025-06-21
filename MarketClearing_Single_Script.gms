****************************************************************************************************************************************************
*                                                        MARKET CLEARING SINGLE SCRIPT                                                             *
*************************************************************************************************-Developed by Joao Augusto Silva Ledo-*************
* This code encompasses 5 ways to solve the market clearing model                                                                                  *
* 1. Primal Market Clearing Model                                                                                                                  *
* 2. Dual Market Clearing Model                                                                                                                    *
* 3. Solving the Market Clearing KKT MCP model as an Optimization Model by using a unitary Objective Function                                      *
* 4. Solving the Market Clearing KKT MCP through solver PATH                                                                                       *
* 5. Solving the Market Clearing PDOC (Primal-dual optimality conditions) MCP model as an Optimization Model by using a unitary Objective Function *
****************************************************************************************************************************************************


***************************************************************************
* SETS
***************************************************************************
Sets
    I All Producers /I1, I2/
    U All Producers' Units /U1, U2/
    J All Consumers /J1/
    C All Consumers' Units /C1/
    UnitGeneratorConect(I, U) /I1.U1, I2.U2/
    UnitConsumerConect(J, C) /J1.C1/;

***************************************************************************
* DATA
***************************************************************************
PARAMETERS
cost(i, u) /I1.U1 = 1, I2.U2 = 2/
utility(j, c) /J1.C1 = 3/
p_max(i, u) /I1.U1 = 6, I2.U2 = 6/
d_max(j, c) /J1.C1 = 10/
Socialwelfare
profit(i)
utilities(j)
Total_Profit
Total_Utility
Big_Producer_Profit
Big_Consumer_Utility
Total_Power
o(i, u)
b(j, c)
ClearedPrice
produced(i, u)
consumed(j, c);

***************************************************************************
* CREATING VARIABLES
***************************************************************************
POSITIVE VARIABLES
mu_p_max(i, u)
mu_d_max(j, c)
mu_p_min(i, u)
mu_d_min(j, c);


VARIABLES
p(i, u)
d(j, c)
lambda;


FREE VARIABLES
OF
Social_Welfare_Primal
Social_Welfare_Dual;

***************************************************************************
* EQUATIONS
***************************************************************************
EQUATIONS
Auxiliar_Objective_Function
Social_Welfare_Primal_OF
Social_Welfare_Dual_OF
balance
producer_boundary_p_min(i, u)
producer_boundary_p_max(i, u)
consumer_boundary_d_min(j, c)
consumer_boundary_d_max(j, c)
Deriv_p(i, u)
Deriv_d(j, c)
comp_p_min(i, u)
comp_p_max(i, u)
comp_d_min(j, c)
comp_d_max(j, c)
Dual_Positivity_mu_p_max(i, u)
Dual_Positivity_mu_d_max(j, c)
Dual_Positivity_mu_p_min(i, u)
Dual_Positivity_mu_d_min(j, c)
SDE;

***************************************************************************
* PRE EXECUTE
***************************************************************************
o(i, u) = cost(i, u);
b(j, c) = utility(j, c);

***************************************************************************
* MODEL
***************************************************************************

* Objective Functions
Auxiliar_Objective_Function.. OF =e= 1;
Social_Welfare_Primal_OF.. Social_Welfare_Primal =e= sum(i, sum(u $ UnitGeneratorConect(i, u), o(i, u)*p(i, u))) -  sum(j, sum(c $ UnitConsumerConect(j, c), b(j, c)*d(j, c)));
Social_Welfare_Dual_OF.. Social_Welfare_Dual =e= - sum(i, sum(u $ UnitGeneratorConect(i, u), mu_p_max(i, u)*p_max(i, u))) - sum(j, sum(c $ UnitConsumerConect(j, c), mu_d_max(j, c)*d_max(j, c)));

* Primal Constraints
balance.. sum(i, sum(u $ UnitGeneratorConect(i, u),p(i, u))) - sum(j, sum(c $ UnitConsumerConect(j, c), d(j, c))) =e= 0;
producer_boundary_p_min(i, u) $ UnitGeneratorConect(i, u).. p(i, u) =g= 0;
producer_boundary_p_max(i, u) $ UnitGeneratorConect(i, u).. -p(i, u) + p_max(i, u) =g= 0;
consumer_boundary_d_min(j, c) $ UnitConsumerConect(j, c).. d(j, c) =g= 0;
consumer_boundary_d_max(j, c) $ UnitConsumerConect(j, c)..  -d(j, c) + d_max(j, c) =g= 0;

* Dual Constraints (Partial derivatives, gradient)
Deriv_p(i, u) $ UnitGeneratorConect(i, u).. + o(i, u) - lambda - mu_p_min(i, u) + mu_p_max(i, u) =e= 0;
Deriv_d(j, c) $ UnitConsumerConect(j, c).. - b(j, c) + lambda - mu_d_min(j, c) + mu_d_max(j, c) =e= 0;

* Complementarities
comp_p_min(i, u) $ UnitGeneratorConect(i, u).. p(i, u)*mu_p_min(i, u) =e= 0;
comp_p_max(i, u) $ UnitGeneratorConect(i, u)..  (p_max(i, u) -  p(i, u))*mu_p_max(i, u) =e= 0;
comp_d_min(j, c) $ UnitConsumerConect(j, c).. d(j, c)*mu_d_min(j, c) =e= 0;
comp_d_max(j, c) $ UnitConsumerConect(j, c).. (d_max(j, c) - d(j, c))*mu_d_max(j, c) =e= 0;

* Strong Duality Equality (SDE)
SDE.. sum(i, sum(u $ UnitGeneratorConect(i, u), o(i, u)*p(i, u))) -  sum(j, sum(c $ UnitConsumerConect(j, c), b(j, c)*d(j, c))) =e= - sum(i, sum(u $ UnitGeneratorConect(i, u), mu_p_max(i, u)*p_max(i, u))) - sum(j, sum(c $ UnitConsumerConect(j, c), mu_d_max(j, c)*d_max(j, c)));

* Dual variables positivity
Dual_Positivity_mu_p_max(i, u) $ UnitGeneratorConect(i, u).. mu_p_max(i, u) =g= 0;
Dual_Positivity_mu_p_min(i, u) $ UnitGeneratorConect(i, u).. mu_p_min(i, u) =g= 0;
Dual_Positivity_mu_d_max(j, c) $ UnitConsumerConect(j, c).. mu_d_max(j, c) =g= 0;
Dual_Positivity_mu_d_min(j, c) $ UnitConsumerConect(j, c).. mu_d_min(j, c) =g= 0;

* choosing a solver
option MIP = CPLEX;
option NLP = KNITRO;
options MCP = PATH;

* Models' instances
MODEL Market_Clearing_Primal /Social_Welfare_Primal_OF, balance, producer_boundary_p_min, producer_boundary_p_max, consumer_boundary_d_min, consumer_boundary_d_max/;
MODEL Market_Clearing_Dual /Social_Welfare_Dual_OF, Deriv_p, Deriv_d, Dual_Positivity_mu_p_max, Dual_Positivity_mu_p_min, Dual_Positivity_mu_d_max, Dual_Positivity_mu_d_min/;
MODEL KKT_Market_Clearing_Auxiliary_OF /Auxiliar_Objective_Function, balance, producer_boundary_p_min, producer_boundary_p_max, consumer_boundary_d_min, consumer_boundary_d_max,
Deriv_p, Deriv_d, Dual_Positivity_mu_p_max, Dual_Positivity_mu_p_min, Dual_Positivity_mu_d_max, Dual_Positivity_mu_d_min,
comp_p_min, comp_p_max, comp_d_min, comp_d_max/;
MODEL KKT_Market_Clearing /balance.lambda, producer_boundary_p_min.mu_p_min, producer_boundary_p_max.mu_p_max
consumer_boundary_d_min.mu_d_min, consumer_boundary_d_max.mu_d_max, Deriv_p.p, Deriv_d.d/;
MODEL Market_Clearing_PC_DC_SDE /Auxiliar_Objective_Function, balance, producer_boundary_p_min, producer_boundary_p_max, consumer_boundary_d_min, consumer_boundary_d_max,
Deriv_p, Deriv_d, Dual_Positivity_mu_p_max, Dual_Positivity_mu_p_min, Dual_Positivity_mu_d_max, Dual_Positivity_mu_d_min, SDE/;


***************************************************************************
*               SOLVING THE MARKET CLEARING PRIMAL MODEL                  *
***************************************************************************
solve Market_Clearing_Primal minimizing Social_Welfare_Primal using MIP;
ClearedPrice = abs(balance.m);
produced(i, u) = p.l(i, u);
consumed(j, c) = d.l(j, c);
Total_Power = sum(i, sum(u $ UnitGeneratorConect(i, u), p.l(i, u)));
profit(i) = sum(u $ UnitGeneratorConect(i, u), abs(balance.m)*p.l(i, u) - cost(i, u)*p.l(i, u));
utilities(j) = sum(c $ UnitConsumerConect(j, c), utility(j, c)*d.l(j, c) - abs(balance.m)*d.l(j, c));
Socialwelfare = sum(i, sum(u $ UnitGeneratorConect(i, u), (abs(balance.m) - cost(i, u))*p.l(i, u))) + sum(j, sum(c $ UnitConsumerConect(j, c), (utility(j, c) - abs(balance.m))*d.l(j, c)));
Total_Profit = sum(i, profit(i));
Total_Utility = sum(j, utilities(j));
display o;
display b;
display ClearedPrice;
display produced;
display consumed;
display profit;
display utilities;
display Socialwelfare;
display Total_Profit;
display Total_Utility;
display Total_Power;
***************************************************************************

***************************************************************************
*                SOLVING THE MARKET CLEARING DUAL MODEL                   *
***************************************************************************
solve Market_Clearing_Dual maximizing Social_Welfare_Dual using MIP;
ClearedPrice = lambda.l;
produced(i, u) = abs(Deriv_p.m(i, u));
consumed(j, c) = abs(Deriv_d.m(j, c));
Total_Power = sum(i, sum(u $ UnitGeneratorConect(i, u), abs(Deriv_p.m(i, u))));
profit(i) = sum(u $ UnitGeneratorConect(i, u), lambda.l*abs(Deriv_p.m(i, u)) - cost(i, u)*abs(Deriv_p.m(i, u)));
utilities(j) = sum(c $ UnitConsumerConect(j, c), utility(j, c)*abs(Deriv_d.m(j, c)) - lambda.l*abs(Deriv_d.m(j, c)));
Socialwelfare = sum(i, sum(u $ UnitGeneratorConect(i, u), (lambda.l - cost(i, u))*abs(Deriv_p.m(i, u)))) + sum(j, sum(c $ UnitConsumerConect(j, c), (utility(j, c) - lambda.l)*abs(Deriv_d.m(j, c))));
Total_Profit = sum(i, profit(i));
Total_Utility = sum(j, utilities(j));
display o;
display b;
display ClearedPrice;
display produced;
display consumed;
display profit;
display profit;
display utilities;
display Socialwelfare;
display Total_Profit;
display Total_Utility;
display Total_Power;
***************************************************************************

**************************************************************************************************************
* SOLVING THE MARKET CLEARING KKT MCP AS AN OPTIMIZATION MODEL USING AN UNITARY AUXILIARY OBJECTIVE FUNCTION *
**************************************************************************************************************
solve KKT_Market_Clearing_Auxiliary_OF maximizing OF using NLP;
ClearedPrice = lambda.l;
produced(i, u) = p.l(i, u);
consumed(j, c) = d.l(j, c);
Total_Power = sum(i, sum(u $ UnitGeneratorConect(i, u), p.l(i, u)));
profit(i) = sum(u $ UnitGeneratorConect(i, u), lambda.l*p.l(i, u) - cost(i, u)*p.l(i, u));
utilities(j) = sum(c $ UnitConsumerConect(j, c), utility(j, c)*d.l(j, c) - lambda.l*d.l(j, c));
Socialwelfare = sum(i, sum(u $ UnitGeneratorConect(i, u), (lambda.l - cost(i, u))*p.l(i, u))) + sum(j, sum(c $ UnitConsumerConect(j, c), (utility(j, c) - lambda.l)*d.l(j, c)));
Total_Profit = sum(i, profit(i));
Total_Utility = sum(j, utilities(j));
display o;
display b;
display ClearedPrice;
display produced;
display consumed;
display profit;
display utilities;
display Socialwelfare;
display Total_Profit;
display Total_Utility;
display Total_Power;
***************************************************************************

***********************************************************
* SOLVING THE MARKET CLEARING KKT MCP THROUGH SOLVER PATH *
***********************************************************
solve KKT_Market_Clearing using MCP;
ClearedPrice = lambda.l;
produced(i, u) = p.l(i, u);
consumed(j, c) = d.l(j, c);
Total_Power = sum(i, sum(u $ UnitGeneratorConect(i, u), p.l(i, u)));
profit(i) = sum(u $ UnitGeneratorConect(i, u), lambda.l*p.l(i, u) - cost(i, u)*p.l(i, u));
utilities(j) = sum(c $ UnitConsumerConect(j, c), utility(j, c)*d.l(j, c) - lambda.l*d.l(j, c));
Socialwelfare = sum(i, sum(u $ UnitGeneratorConect(i, u), (lambda.l - cost(i, u))*p.l(i, u))) + sum(j, sum(c $ UnitConsumerConect(j, c), (utility(j, c) - lambda.l)*d.l(j, c)));
Total_Profit = sum(i, profit(i));
Total_Utility = sum(j, utilities(j));
display o;
display b;
display ClearedPrice;
display produced;
display consumed;
display profit;
display utilities;
display Socialwelfare;
display Total_Profit;
display Total_Utility;
display Total_Power;
***************************************************************************


***************************************************************************************************************************************************
* SOLVING THE MARKET CLEARING PDOC (Primal-dual Optimality conditions) MCP AS AN OPTIMIZATION MODEL USING AN UNITARY AUXILIARY OBJECTIVE FUNCTION *
***************************************************************************************************************************************************
solve Market_Clearing_PC_DC_SDE maximizing OF using MIP;
ClearedPrice = lambda.l;
produced(i, u) = p.l(i, u);
consumed(j, c) = d.l(j, c);
Total_Power = sum(i, sum(u $ UnitGeneratorConect(i, u), p.l(i, u)));
profit(i) = sum(u $ UnitGeneratorConect(i, u), lambda.l*p.l(i, u) - cost(i, u)*p.l(i, u));
utilities(j) = sum(c $ UnitConsumerConect(j, c), utility(j, c)*d.l(j, c) - lambda.l*d.l(j, c));
Socialwelfare = sum(i, sum(u $ UnitGeneratorConect(i, u), (lambda.l - cost(i, u))*p.l(i, u))) + sum(j, sum(c $ UnitConsumerConect(j, c), (utility(j, c) - lambda.l)*d.l(j, c)));
Total_Profit = sum(i, profit(i));
Total_Utility = sum(j, utilities(j));
display o;
display b;
display ClearedPrice;
display produced;
display consumed;
display profit;
display utilities;
display Socialwelfare;
display Total_Profit;
display Total_Utility;
display Total_Power;
***************************************************************************
