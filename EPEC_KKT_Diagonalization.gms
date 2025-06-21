********************************************************************************************************************************************************
*                                                                   EPEC KKT DIAGONALIZATION                                                           *
*************************************************************************************************-Developed by Joao Augusto Silva Ledo-*****************
* This is an EPEC model achieved by diagonalization of multiples strategic bilevel models in equilibrium where the upper-level embodies the            *
* strategic producer or strategic consumer and theirs respetive lower-level embodies the entire market clearing model, therefore creating an           *
* Multi-leader-single-follower equilibrium. Each of the respetively lower-level models are replaced by its KKT optimality conditions and solved by     *
* an approach called diagolalization                                                                                                                   *
* NOTE 1. THE KEY POINT IN THIS CODE ARE THE SUBSETS OF STRATEGIC AND NON-STRATEGIC PRODUCERS AND CONSUMERS ITERATIVELY SOLVED                         *
* NOTE 2. NOTICE THE SUBSETS DOESN'T DISTIGUISHES STRATEGICS FROM NON-STRATEGICS AGENTS AT ITS CREATION, BUT LATER ON BY                               *
* TURNING ON AND OFF ITS VALUES IN A WHILE LOOP, DEPENDING ON THE STRATEGIC AGENT AND THE MODEL.                                                       *
* NOTE 3. ALWAYS CREATE PARAMETERS, VARIABLES AND EQUATIONS USING SETS AND NOT SUBSETS, SINCE SUBSETS WILL CHANGE ITS VALUES ITERARIVELY. THEREFORE    *
* USE THE SUBSETS TO DISTIGUISHES THE STRATEGIC AGENTS FROM THE NON-STRATEGIC ONES WHEN CREATING THE CONSTRAINTS ONLY!!                                *
********************************************************************************************************************************************************

***************************************************************************
* SETS
***************************************************************************
Sets
    I Producer /I1, I2/
    Y(I) Strategic Producers subset /I1, I2/
    K(I) Non-Strategic Producers subset /I1, I2/
    J Consumers /J1/
    Z(J) Strategic Consumers/J1/
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
    b_aux(j, c) Non-strategic consumers' bids
    o_previus(i, u)
    b_previus(j, c)
    kk;
    

***************************************************************************
* DECLARATION OF VARIABLES
***************************************************************************

Variables
    p(i, u) Power produced
    d(j, c) Power consumed;
    o(i, u) Strategic producers' offers
    b(j, c) Strategic Consumer' Bids
    lambda Cleared price;
    
Positive Variables
    mu_p_min(i, u) dual variable associated to variable p lower bound constraint
    mu_p_max(i, u) dual variable associated to variable p upper bound constraint
    mu_d_min(j, c) dual variable associated to variable d lower bound constraint
    mu_d_max(j, c) dual variable associated to variable d upper bound constraint;

Free Variable
     OF_Producer Producer objective function variable
     OF_Consumer Consumer objective function variable;


***************************************************************************
* EQUATIONS
***************************************************************************

Equations
    Objective_Function_Producer
    Objective_Function_Consumer
    balance
    Strategic_Offering_Boundary(i, u)
    Strategic_Bidding_Boundary(j, c)
    producer_upperboundary(i, u)
    producer_lowerboundary(i, u)
    consumer_upperboundary(j, c)
    consumer_lowerboundary(j, c)
    Deriv_p_S(i, u)
    Deriv_p_NS(i, u)
    Deriv_d_S(j, c)
    Deriv_d_NS(j, c)
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

* Non-strategic offers and bids *
o_aux(i, u) $ UnitGeneratorConect(i, u) = cost(i, u);
b_aux(j, c) $ UnitConsumerConect(j, c) = max_utility(j, c);

*    p.l(i, u) = aux(i, u);
*    d.l(j, c) = d_max(j, c);

    
***************************************************************************
* MODEL
***************************************************************************

* Objective function
Objective_Function_Producer.. OF_Producer =e= sum(y, sum(u $ UnitGeneratorConect(y, u), lambda*p(y, u) - cost(y, u)*p(y, u)));
Objective_Function_Consumer.. OF_Consumer =e= sum(z, sum(c $ UnitConsumerConect(z, c), max_utility(z, c)*d(z, c) - d(z, c)*lambda));

* Constraints *

* Upper-level constraints *
Strategic_Offering_Boundary(y, u) $ UnitGeneratorConect(y, u).. o(y, u) =g= cost(y, u);
Strategic_Bidding_Boundary(z, c) $ UnitConsumerConect(z, c).. b(z, c) =l= max_utility(z, c);

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
Deriv_d_S(z, c) $ UnitConsumerConect(z, c).. -b(z, c) + lambda - mu_d_min(z, c) + mu_d_max(z, c) =e= 0;
Deriv_d_NS(l, c) $ UnitConsumerConect(l, c).. -b_aux(l, c) + lambda - mu_d_min(l, c) + mu_d_max(l, c) =e= 0;

* Lower-level complementary constraints
comp_p_min(i, u) $ UnitGeneratorConect(i, u).. p(i, u)*mu_p_min(i, u) =e= 0;
comp_p_max(i, u) $ UnitGeneratorConect(i, u).. (p_max(i, u)- p(i, u))*mu_p_max(i, u) =e= 0;
comp_d_min(j, c) $ UnitConsumerConect(j, c).. d(j, c)*mu_d_min(j, c) =e= 0;
comp_d_max(j, c) $ UnitConsumerConect(j, c).. (d_max(j, c) - d(j, c))*mu_d_max(j, c) =e= 0;

* Dual variables positivity
Dual_Positivity_mu_p_min(i, u) $ UnitGeneratorConect(i, u).. mu_p_min(i, u) =g= 0;
Dual_Positivity_mu_p_max(i, u) $ UnitGeneratorConect(i, u).. mu_p_max(i, u) =g= 0;
Dual_Positivity_mu_d_min(j, c) $ UnitConsumerConect(j, c).. mu_d_min(j, c) =g= 0;
Dual_Positivity_mu_d_max(j, c) $ UnitConsumerConect(j, c).. mu_d_max(j, c) =g= 0;

* Sover option
option NLP = CONOPT;

* Model's instances

Model MPEC_StrategicProducer_KKT /Objective_Function_Producer, Strategic_Offering_Boundary, balance, producer_lowerboundary, producer_upperboundary,
consumer_lowerboundary, consumer_upperboundary, Deriv_p_S, Deriv_p_NS, Deriv_d_NS, comp_p_min, comp_p_max, comp_d_min, comp_d_max,
Dual_Positivity_mu_p_min, Dual_Positivity_mu_p_max, Dual_Positivity_mu_d_min, Dual_Positivity_mu_d_max/;

Model MPEC_StrategicConsumer_KKT /Objective_Function_Consumer, Strategic_Bidding_Boundary, balance, producer_lowerboundary, producer_upperboundary,
consumer_lowerboundary, consumer_upperboundary, Deriv_d_S, Deriv_d_NS, Deriv_p_NS, comp_p_min, comp_p_max, comp_d_min, comp_d_max,
Dual_Positivity_mu_p_min, Dual_Positivity_mu_p_max, Dual_Positivity_mu_d_min, Dual_Positivity_mu_d_max/;


***************************************************************************
*               SOLVING MPEC PRODUCER 1 STRATEGIC MODEL                   *
***************************************************************************
Y('I1') = yes;
Y('I2') = no;
K('I1') = no;
K('I2') = yes;
Z('J1') = no;
L('J1') = yes;
solve MPEC_StrategicProducer_KKT maximizing OF_Producer using NLP;

* SWAP MOVE: SAVING THE PREVIUS NON-STRATEGIC OFFERS ARRAY AND UPDATING THE NON-STRATEGIC ARRAY WITH THE CURRENT STRATEGIC OUTPUT ONLY INTO THE CURRENT STRATEGIC POSITION Y *
o_previus(i, u) = o_aux(i, u);
o_aux(y, u) = o.l(y, u);
******************************************************************************************************************************************************************************

* POST EXECUTE *
Cleared_Price = lambda.l;
profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
Social_Welfare = sum(i, profit(i)) + sum(j, utility(j));
display o.l;
display o_aux;
display b_aux;
display Cleared_Price;
display Social_Welfare;
display profit;
display utility;
***************************************************************************

***************************************************************************
*               SOLVING MPEC PRODUCER 2 STRATEGIC MODEL                   *
***************************************************************************
Y('I1') = no;
Y('I2') = yes;
K('I1') = yes;
K('I2') = no;
Z('J1') = no;
L('J1') = yes;
solve MPEC_StrategicProducer_KKT maximizing OF_Producer using NLP;

* SWAP MOVE: SAVING THE PREVIUS NON-STRATEGIC OFFERS ARRAY AND UPDATING THE NON-STRATEGIC ARRAY WITH THE CURRENT STRATEGIC OUTPUT ONLY INTO THE CURRENT STRATEGIC POSITION Y *
o_previus(i, u) = o_aux(i, u);
o_aux(y, u) = o.l(y, u);
******************************************************************************************************************************************************************************

* POST EXECUTE *
Cleared_Price = lambda.l;
profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
Social_Welfare = sum(i, profit(i)) + sum(j, utility(j));
display o.l;
display o_aux;
display b_aux;
display Cleared_Price;
display Social_Welfare;
display profit;
display utility;
***************************************************************************

***************************************************************************
*               SOLVING MPEC CONSUMER 1 STRATEGIC MODEL                   *
***************************************************************************
Y('I1') = no;
Y('I2') = no;
K('I1') = yes;
K('I2') = yes;
Z('J1') = yes;
L('J1') = no;
solve MPEC_StrategicConsumer_KKT maximizing OF_Consumer using NLP;

* SWAP MOVE: SAVING THE PREVIUS NON-STRATEGIC BIDS ARRAY AND UPDATING THE NON-STRATEGIC ARRAY WITH THE CURRENT STRATEGIC OUTPUT ONLY INTO THE CURRENT STRATEGIC POSITION Z *
b_previus(j, c) = b_aux(j, c);
b_aux(z, c) = b.l(z, c);
****************************************************************************************************************************************************************************

* POST EXECUTE *
Cleared_Price = lambda.l;
profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
Social_Welfare = sum(i, profit(i)) + sum(j, utility(j));
display b.l;
display b_aux;
display o_aux;
display Cleared_Price;
display Social_Welfare;
display profit;
display utility;
***************************************************************************

* FIRST ITERATION IS CLEARED
kk = 1;
* STARTING THE LOOP RESPECTING THE STOP CONDITIONS
while((kk le 100) and (sum(i, sum(u $ UnitGeneratorConect(i, u), abs(o_previus(i, u) - o_aux(i, u)))) ge 0.1) or (sum(j, sum(c $ UnitConsumerConect(j, c), abs(b_previus(j, c) - b_aux(j, c)))) ge 0.1),
***************************************************************************
*               SOLVING MPEC PRODUCER 1 STRATEGIC MODEL                   *
***************************************************************************
    Y('I1') = yes;
    Y('I2') = no;
    K('I1') = no;
    K('I2') = yes;
    Z('J1') = no;
    L('J1') = yes;
    solve MPEC_StrategicProducer_KKT maximizing OF_Producer using NLP;
* SWAP MOVE: SAVING THE PREVIUS NON-STRATEGIC OFFERS ARRAY AND UPDATING THE NON-STRATEGIC ARRAY WITH THE CURRENT STRATEGIC OUTPUT ONLY INTO THE CURRENT STRATEGIC POSITION Y *
    o_previus(i, u) = o_aux(i, u);
    o_aux(y, u) = o.l(y, u);
******************************************************************************************************************************************************************************
* POST EXECUTE *
    Cleared_Price = lambda.l;
    profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
    utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
    Social_Welfare = sum(i, profit(i)) + sum(j, utility(j));
    display o.l;
    display o_aux;
    display b_aux;
    display Cleared_Price;
    display Social_Welfare;
    display profit;
    display utility;
***************************************************************************
    
***************************************************************************
*               SOLVING MPEC PRODUCER 2 STRATEGIC MODEL                   *
***************************************************************************
    Y('I1') = no;
    Y('I2') = yes;
    K('I1') = yes;
    K('I2') = no;
    Z('J1') = no;
    L('J1') = yes;
    solve MPEC_StrategicProducer_KKT maximizing OF_Producer using NLP;
* SWAP MOVE: SAVING THE PREVIUS NON-STRATEGIC OFFERS ARRAY AND UPDATING THE NON-STRATEGIC ARRAY WITH THE CURRENT STRATEGIC OUTPUT ONLY INTO THE CURRENT STRATEGIC POSITION Y *
    o_previus(i, u) = o_aux(i, u);
    o_aux(y, u) = o.l(y, u);
******************************************************************************************************************************************************************************    
* POST EXECUTE *
    Cleared_Price = lambda.l;
    profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
    utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
    Social_Welfare = sum(i, profit(i)) + sum(j, utility(j));
    display o.l;
    display o_aux;
    display b_aux;
    display Cleared_Price;
    display Social_Welfare;
    display profit;
    display utility;
***************************************************************************
    
***************************************************************************
*               SOLVING MPEC CONSUMER 1 STRATEGIC MODEL                   *
***************************************************************************
    Y('I1') = no;
    Y('I2') = no;
    K('I1') = yes;
    K('I2') = yes;
    Z('J1') = yes;
    L('J1') = no;
    solve MPEC_StrategicConsumer_KKT maximizing OF_Consumer using NLP;
* SWAP MOVE: SAVING THE PREVIUS NON-STRATEGIC BIDS ARRAY AND UPDATING THE NON-STRATEGIC ARRAY WITH THE CURRENT STRATEGIC OUTPUT ONLY INTO THE CURRENT STRATEGIC POSITION Z *
    b_previus(j, c) = b_aux(j, c);
    b_aux(z, c) = b.l(z, c);
****************************************************************************************************************************************************************************** 
* POST EXECUTE *
    Cleared_Price = lambda.l;
    profit(i) = sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*Cleared_Price) - sum(u $ UnitGeneratorConect(i, u), p.l(i, u)*cost(i, u));
    utility(j) = sum(c $ UnitConsumerConect(j, c), d.l(j, c)*max_utility(j, c)) -  sum(c $ UnitConsumerConect(j, c), d.l(j, c)*Cleared_Price);
    Social_Welfare = sum(i, profit(i)) + sum(j, utility(j));
    display b.l;
    display b_aux;
    display o_aux;
    display Cleared_Price;
    display Social_Welfare;
    display profit;
    display utility;
***************************************************************************

* NEXT ITERATION IS CLEARED
    kk = kk + 1;
    display kk;
);
