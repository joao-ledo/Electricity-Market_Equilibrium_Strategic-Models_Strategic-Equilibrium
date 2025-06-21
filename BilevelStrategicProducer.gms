********************************************************************************************************************************************************
*                                                                 MPECy STRATEGIC PRODUCER                                                             *
*************************************************************************************************-Developed by Joao Augusto Silva Ledo-*****************
* This is a bilevel model (Stackelberg Game) which the upper-level embodies the strategic producer and the lower-level the entire market clearing      *
* that is replaced by 2 different optimality conditions:                                                                                               *
* 1. The lower-level model is replaced by its KKT set of optimality conditions                                                                         *
* 2. The lower-level model is replaced by its PDOC (Primal constraints, dual constraints, strong duality equality) set of optimality conditions        *
* NOTE 1. THE KEY POINT IN THIS CODE ARE THE SUBSETS OF STRATEGIC AND NON-STRATEGIC PRODUCERS AND CONSUMERS                                            *
* NOTE 2. NOTICE THE SUBSETS DOESN'T DISTIGUISHES STRATEGICS FROM NON-STRATEGICS AGENTS AT ITS CREATION, BUT LATER ON BY TURNING ON AND OFF ITS VALUES *
* NOTE 3. ALWAYS CREATE PARAMETERS, VARIABLES AND EQUATIONS USING SETS AND NOT SUBSETS, SINCE SUBSETS WILL CHANGE ITS VALUES. USE THE SUBSETS          *
* TO DISTIGUISHES THE STRATEGIC AGENTS FROM THE NON-STRATEGIC ONES WHEN CREATING THE CONSTRAINTS ONLY                                                  *
********************************************************************************************************************************************************


***************************************************************************
* SETS
***************************************************************************
Sets
    I Producers /I1, I2/
    Y(I) Strategic Producers subset /I1, I2/
    K(I) Non-Strategic Producers subset /I1, I2/
    J Consumers /J1/
    Z(J) Strategic Consumers /J1/
    L(J) Non-strategic Consumers /J1/
    U Producers' units /U1, U2/
    C Consumers' demands /C1/
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
    o_aux(i, u) Non-strategic producers' offers
    b(j, c) Non-strategic consumers' bids;
    

***************************************************************************
* CREATING VARIABLES
***************************************************************************

Variables
    p(i, u) Power produced
    d(j, c) Power consumed;
    o(i, u) Strategic producer' offers
    lambda Cleared price;
    
Positive Variables
    mu_p_min(i, u) dual variable associated to variable p lower bound constraint
    mu_p_max(i, u) dual variable associated to variable p upper bound constraint
    mu_d_min(j, c) dual variable associated to variable d lower bound constraint
    mu_d_max(j, c) dual variable associated to variable d upper bound constraint;

Free Variable
     OF objective function variable;


***************************************************************************
* EQUATIONS
***************************************************************************

Equations
    Objective_Function
    balance
    Strategic_Offering_Boundary(i, u)
    producer_upperboundary(i, u)
    producer_lowerboundary(i, u)
    consumer_upperboundary(j, c)
    consumer_lowerboundary(j, c)
    Deriv_p_S(i, u)
    Deriv_p_NS(i, u)
    Deriv_d(j, c)
    comp_p_min(i, u)
    comp_p_max(i, u)
    comp_d_min(j, c)
    comp_d_max(j, c)
    Dual_Positivity_mu_p_max(i, u)
    Dual_Positivity_mu_d_max(j, c)
    Dual_Positivity_mu_p_min(i, u)
    Dual_Positivity_mu_d_min(j, c)
    SDE_Producer;

***************************************************************************
* PRE EXECUTE
***************************************************************************

* Non-strategic offers and bids *
o_aux(k, u) $ UnitGeneratorConect(k, u) = cost(k, u);
b(j, c) = max_utility(j, c);

*    p.l(i, u) = aux(i, u);
*    d.l(j, c) = d_max(j, c);
    
***************************************************************************
* MODEL
***************************************************************************

* Objective function
Objective_Function.. OF =e= sum(y, sum(u $ UnitGeneratorConect(y, u), lambda*p(y, u) - cost(y, u)*p(y, u)));

* Constraints *

* Upper-level constraints *
Strategic_Offering_Boundary(y, u) $ UnitGeneratorConect(y, u).. o(y, u) =g= cost(y, u);

* Lower-level primal constraints
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

* Lower-level partial derivatives (dual constraints)
Deriv_p_S(y, u) $ UnitGeneratorConect(y, u).. o(y, u) - lambda - mu_p_min(y, u) + mu_p_max(y, u) =e= 0;
Deriv_p_NS(k, u) $ UnitGeneratorConect(k, u).. o_aux(k, u) - lambda - mu_p_min(k, u) + mu_p_max(k, u) =e= 0;
Deriv_d(j, c) $ UnitConsumerConect(j, c).. -b(j, c) + lambda - mu_d_min(j, c) + mu_d_max(j, c) =e= 0;

* Lower-level complementary constraints
comp_p_min(i, u) $ UnitGeneratorConect(i, u).. p(i, u)*mu_p_min(i, u) =e= 0;
comp_p_max(i, u) $ UnitGeneratorConect(i, u).. (p_max(i, u)- p(i, u))*mu_p_max(i, u) =e= 0;
comp_d_min(j, c) $ UnitConsumerConect(j, c).. d(j, c)*mu_d_min(j, c) =e= 0;
comp_d_max(j, c) $ UnitConsumerConect(j, c).. (d_max(j, c) - d(j, c))*mu_d_max(j, c) =e= 0;

* Strong Duality Equality
SDE_Producer.. sum(y, sum(u $ UnitGeneratorConect(y, u), o(y, u)*p(y, u))) + sum(k, sum(u $ UnitGeneratorConect(k, u), o_aux(k, u)*p(k, u))) - sum(j, sum(c $ UnitConsumerConect(j, c), b(j, c)*d(j, c))) =e= - sum(i, sum(u $ UnitGeneratorConect(i, u), mu_p_max(i, u)*p_max(i, u))) - sum(j, sum(c $ UnitConsumerConect(j, c), mu_d_max(j, c)*d_max(j, c)));

* Dual variables positivity
Dual_Positivity_mu_p_min(i, u) $ UnitGeneratorConect(i, u).. mu_p_min(i, u) =g= 0;
Dual_Positivity_mu_p_max(i, u) $ UnitGeneratorConect(i, u).. mu_p_max(i, u) =g= 0;
Dual_Positivity_mu_d_min(j, c) $ UnitConsumerConect(j, c).. mu_d_min(j, c) =g= 0;
Dual_Positivity_mu_d_max(j, c) $ UnitConsumerConect(j, c).. mu_d_max(j, c) =g= 0;

* Sover option
option NLP = BARON;

* Model's instances

Model MPEC_StrategicProducer_KKT /Objective_Function, Strategic_Offering_Boundary, balance, producer_lowerboundary, producer_upperboundary,
consumer_lowerboundary, consumer_upperboundary, Deriv_p_S, Deriv_p_NS, Deriv_d, comp_p_min, comp_p_max, comp_d_min, comp_d_max,
Dual_Positivity_mu_p_min, Dual_Positivity_mu_p_max, Dual_Positivity_mu_d_min, Dual_Positivity_mu_d_max/;

Model MPEC_StrategicProducer_PC_DC_SDE /Objective_Function, Strategic_Offering_Boundary, balance, producer_lowerboundary, producer_upperboundary,
consumer_lowerboundary, consumer_upperboundary, Deriv_p_S, Deriv_p_NS, Deriv_d, SDE_Producer,
Dual_Positivity_mu_p_min, Dual_Positivity_mu_p_max, Dual_Positivity_mu_d_min, Dual_Positivity_mu_d_max/;

***************************************************************************
*    SOLVING MPEC_y WHICH ITS LOWER-LEVEL HAS BEEN REPLACED BY ITS KKT    *
***************************************************************************
* Turning ON and OFF vallues from subsets deppending on whose going to be strategic or not when running the code
Y('I1') = yes;
Y('I2') = no;
K('I1') = no;
K('I2') = yes;
Z('J1') = no;
L('J1') = yes;
solve MPEC_StrategicProducer_KKT maximizing OF using NLP;
* POST EXECUTE *
Cleared_Price = lambda.l;
profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
Social_Welfare = sum(i, profit(i)) + sum(j, utility(j));
display o.l;
display o_aux;
display b;
display Cleared_Price;
display Social_Welfare;
display profit;
display utility;


***************************************************************************
*    SOLVING MPEC_y WHICH ITS LOWER-LEVEL HAS BEEN REPLACED BY ITS PDOC   *
***************************************************************************
* Turning ON and OFF vallues from subsets deppending on whose going to be strategic or not when running the code
Y('I1') = yes;
Y('I2') = no;
K('I1') = no;
K('I2') = yes;
Z('J1') = no;
L('J1') = yes;
solve MPEC_StrategicProducer_PC_DC_SDE maximizing OF using NLP;
* POST EXECUTE *
Cleared_Price = lambda.l;
profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
Social_Welfare = sum(i, profit(i)) + sum(j, utility(j));
display o.l;
display o_aux;
display b;
display Cleared_Price;
display Social_Welfare;
display profit;
display utility;
