; Time: 0.01 seconds
(define (problem GROUNDED-TRUCK-6)
(:domain GROUNDED-TRUCKS-TIME)
(:init
(FOO)
(at_package8_l3)
(at_package7_l3)
(at_package6_l1)
(at_package5_l1)
(at_package4_l2)
(at_package3_l2)
(at_package2_l2)
(at_package1_l2)
(free_a2_truck1)
(free_a1_truck1)
(at_truck1_l1)
)
(:goal
(and
(delivered_package8_l1)
(delivered_package7_l1)
(delivered_package6_l2)
(delivered_package5_l2)
(delivered_package4_l3)
(delivered_package3_l1)
(delivered_package2_l3)
(delivered_package1_l3)
)
)
(:metric MINIMIZE (TOTAL-TIME))
)