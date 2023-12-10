(define (problem schedule-47-1)
(:domain schedule)
(:objects
    A2
    Z1
    W1
    V1
    U1
    S1
    R1
    P1
    Q1
    O1
    N1
    M1
    L1
    K1
    J1
    I1
    H1
    G1
    F1
    E1
    D1
    C1
    B1
    A1
    Z0
    W0
    V0
    U0
    S0
    R0
    P0
    Q0
    O0
    N0
    M0
    L0
    K0
    J0
    I0
    H0
    G0
    F0
    E0
    D0
    C0
    CIRCULAR
    TWO
    THREE
    BLUE
    YELLOW
    BACK
    RED
    B0
    FRONT
    ONE
    BLACK
    OBLONG
    A0
)
(:init
    (SHAPE A0 CIRCULAR)
    (SURFACE-CONDITION A0 POLISHED)
    (PAINTED A0 RED)
    (HAS-HOLE A0 TWO FRONT)
    (TEMPERATURE A0 COLD)
    (SHAPE B0 OBLONG)
    (SURFACE-CONDITION B0 ROUGH)
    (PAINTED B0 BLUE)
    (HAS-HOLE B0 ONE BACK)
    (TEMPERATURE B0 COLD)
    (SHAPE C0 CIRCULAR)
    (SURFACE-CONDITION C0 SMOOTH)
    (PAINTED C0 BLACK)
    (HAS-HOLE C0 THREE FRONT)
    (TEMPERATURE C0 COLD)
    (SHAPE D0 CYLINDRICAL)
    (SURFACE-CONDITION D0 POLISHED)
    (PAINTED D0 YELLOW)
    (HAS-HOLE D0 ONE BACK)
    (TEMPERATURE D0 COLD)
    (SHAPE E0 CIRCULAR)
    (SURFACE-CONDITION E0 POLISHED)
    (PAINTED E0 BLACK)
    (HAS-HOLE E0 THREE FRONT)
    (TEMPERATURE E0 COLD)
    (SHAPE F0 CYLINDRICAL)
    (SURFACE-CONDITION F0 POLISHED)
    (PAINTED F0 RED)
    (HAS-HOLE F0 ONE BACK)
    (TEMPERATURE F0 COLD)
    (SHAPE G0 CYLINDRICAL)
    (SURFACE-CONDITION G0 POLISHED)
    (PAINTED G0 YELLOW)
    (HAS-HOLE G0 THREE FRONT)
    (TEMPERATURE G0 COLD)
    (SHAPE H0 CIRCULAR)
    (SURFACE-CONDITION H0 SMOOTH)
    (PAINTED H0 BLUE)
    (HAS-HOLE H0 TWO FRONT)
    (TEMPERATURE H0 COLD)
    (SHAPE I0 CIRCULAR)
    (SURFACE-CONDITION I0 ROUGH)
    (PAINTED I0 BLACK)
    (HAS-HOLE I0 THREE BACK)
    (TEMPERATURE I0 COLD)
    (SHAPE J0 OBLONG)
    (SURFACE-CONDITION J0 POLISHED)
    (PAINTED J0 YELLOW)
    (HAS-HOLE J0 THREE FRONT)
    (TEMPERATURE J0 COLD)
    (SHAPE K0 CIRCULAR)
    (SURFACE-CONDITION K0 ROUGH)
    (PAINTED K0 RED)
    (HAS-HOLE K0 THREE BACK)
    (TEMPERATURE K0 COLD)
    (SHAPE L0 CIRCULAR)
    (SURFACE-CONDITION L0 ROUGH)
    (PAINTED L0 RED)
    (HAS-HOLE L0 THREE FRONT)
    (TEMPERATURE L0 COLD)
    (SHAPE M0 OBLONG)
    (SURFACE-CONDITION M0 SMOOTH)
    (PAINTED M0 RED)
    (HAS-HOLE M0 TWO FRONT)
    (TEMPERATURE M0 COLD)
    (SHAPE N0 CIRCULAR)
    (SURFACE-CONDITION N0 ROUGH)
    (PAINTED N0 RED)
    (HAS-HOLE N0 THREE FRONT)
    (TEMPERATURE N0 COLD)
    (SHAPE O0 OBLONG)
    (SURFACE-CONDITION O0 ROUGH)
    (PAINTED O0 YELLOW)
    (HAS-HOLE O0 ONE FRONT)
    (TEMPERATURE O0 COLD)
    (SHAPE Q0 CIRCULAR)
    (SURFACE-CONDITION Q0 SMOOTH)
    (PAINTED Q0 BLUE)
    (HAS-HOLE Q0 ONE BACK)
    (TEMPERATURE Q0 COLD)
    (SHAPE P0 CYLINDRICAL)
    (SURFACE-CONDITION P0 SMOOTH)
    (PAINTED P0 YELLOW)
    (HAS-HOLE P0 ONE BACK)
    (TEMPERATURE P0 COLD)
    (SHAPE R0 CYLINDRICAL)
    (SURFACE-CONDITION R0 ROUGH)
    (PAINTED R0 RED)
    (HAS-HOLE R0 TWO FRONT)
    (TEMPERATURE R0 COLD)
    (SHAPE S0 CYLINDRICAL)
    (SURFACE-CONDITION S0 SMOOTH)
    (PAINTED S0 BLACK)
    (HAS-HOLE S0 THREE FRONT)
    (TEMPERATURE S0 COLD)
    (SHAPE U0 OBLONG)
    (SURFACE-CONDITION U0 SMOOTH)
    (PAINTED U0 BLACK)
    (HAS-HOLE U0 TWO BACK)
    (TEMPERATURE U0 COLD)
    (SHAPE V0 CIRCULAR)
    (SURFACE-CONDITION V0 POLISHED)
    (PAINTED V0 BLACK)
    (HAS-HOLE V0 TWO BACK)
    (TEMPERATURE V0 COLD)
    (SHAPE W0 CIRCULAR)
    (SURFACE-CONDITION W0 POLISHED)
    (PAINTED W0 YELLOW)
    (HAS-HOLE W0 TWO BACK)
    (TEMPERATURE W0 COLD)
    (SHAPE Z0 CIRCULAR)
    (SURFACE-CONDITION Z0 SMOOTH)
    (PAINTED Z0 RED)
    (HAS-HOLE Z0 THREE BACK)
    (TEMPERATURE Z0 COLD)
    (SHAPE A1 OBLONG)
    (SURFACE-CONDITION A1 POLISHED)
    (PAINTED A1 YELLOW)
    (HAS-HOLE A1 TWO FRONT)
    (TEMPERATURE A1 COLD)
    (SHAPE B1 OBLONG)
    (SURFACE-CONDITION B1 ROUGH)
    (PAINTED B1 BLACK)
    (HAS-HOLE B1 THREE BACK)
    (TEMPERATURE B1 COLD)
    (SHAPE C1 OBLONG)
    (SURFACE-CONDITION C1 ROUGH)
    (PAINTED C1 BLUE)
    (HAS-HOLE C1 THREE BACK)
    (TEMPERATURE C1 COLD)
    (SHAPE D1 OBLONG)
    (SURFACE-CONDITION D1 POLISHED)
    (PAINTED D1 BLACK)
    (HAS-HOLE D1 THREE FRONT)
    (TEMPERATURE D1 COLD)
    (SHAPE E1 OBLONG)
    (SURFACE-CONDITION E1 POLISHED)
    (PAINTED E1 RED)
    (HAS-HOLE E1 THREE FRONT)
    (TEMPERATURE E1 COLD)
    (SHAPE F1 CIRCULAR)
    (SURFACE-CONDITION F1 POLISHED)
    (PAINTED F1 YELLOW)
    (HAS-HOLE F1 THREE FRONT)
    (TEMPERATURE F1 COLD)
    (SHAPE G1 CYLINDRICAL)
    (SURFACE-CONDITION G1 SMOOTH)
    (PAINTED G1 RED)
    (HAS-HOLE G1 ONE BACK)
    (TEMPERATURE G1 COLD)
    (SHAPE H1 CIRCULAR)
    (SURFACE-CONDITION H1 SMOOTH)
    (PAINTED H1 RED)
    (HAS-HOLE H1 TWO FRONT)
    (TEMPERATURE H1 COLD)
    (SHAPE I1 CYLINDRICAL)
    (SURFACE-CONDITION I1 SMOOTH)
    (PAINTED I1 BLACK)
    (HAS-HOLE I1 TWO BACK)
    (TEMPERATURE I1 COLD)
    (SHAPE J1 CIRCULAR)
    (SURFACE-CONDITION J1 POLISHED)
    (PAINTED J1 YELLOW)
    (HAS-HOLE J1 TWO FRONT)
    (TEMPERATURE J1 COLD)
    (SHAPE K1 CIRCULAR)
    (SURFACE-CONDITION K1 ROUGH)
    (PAINTED K1 BLACK)
    (HAS-HOLE K1 ONE BACK)
    (TEMPERATURE K1 COLD)
    (SHAPE L1 OBLONG)
    (SURFACE-CONDITION L1 SMOOTH)
    (PAINTED L1 BLUE)
    (HAS-HOLE L1 ONE BACK)
    (TEMPERATURE L1 COLD)
    (SHAPE M1 CIRCULAR)
    (SURFACE-CONDITION M1 SMOOTH)
    (PAINTED M1 BLUE)
    (HAS-HOLE M1 THREE BACK)
    (TEMPERATURE M1 COLD)
    (SHAPE N1 CYLINDRICAL)
    (SURFACE-CONDITION N1 SMOOTH)
    (PAINTED N1 BLUE)
    (HAS-HOLE N1 THREE BACK)
    (TEMPERATURE N1 COLD)
    (SHAPE O1 CIRCULAR)
    (SURFACE-CONDITION O1 ROUGH)
    (PAINTED O1 BLUE)
    (HAS-HOLE O1 THREE BACK)
    (TEMPERATURE O1 COLD)
    (SHAPE Q1 CIRCULAR)
    (SURFACE-CONDITION Q1 SMOOTH)
    (PAINTED Q1 YELLOW)
    (HAS-HOLE Q1 ONE BACK)
    (TEMPERATURE Q1 COLD)
    (SHAPE P1 OBLONG)
    (SURFACE-CONDITION P1 ROUGH)
    (PAINTED P1 YELLOW)
    (HAS-HOLE P1 ONE BACK)
    (TEMPERATURE P1 COLD)
    (SHAPE R1 CIRCULAR)
    (SURFACE-CONDITION R1 ROUGH)
    (PAINTED R1 BLACK)
    (HAS-HOLE R1 TWO BACK)
    (TEMPERATURE R1 COLD)
    (SHAPE S1 CIRCULAR)
    (SURFACE-CONDITION S1 ROUGH)
    (PAINTED S1 YELLOW)
    (HAS-HOLE S1 TWO FRONT)
    (TEMPERATURE S1 COLD)
    (SHAPE U1 OBLONG)
    (SURFACE-CONDITION U1 SMOOTH)
    (PAINTED U1 BLACK)
    (HAS-HOLE U1 TWO BACK)
    (TEMPERATURE U1 COLD)
    (SHAPE V1 CYLINDRICAL)
    (SURFACE-CONDITION V1 ROUGH)
    (PAINTED V1 YELLOW)
    (HAS-HOLE V1 ONE FRONT)
    (TEMPERATURE V1 COLD)
    (SHAPE W1 CYLINDRICAL)
    (SURFACE-CONDITION W1 SMOOTH)
    (PAINTED W1 BLACK)
    (HAS-HOLE W1 THREE FRONT)
    (TEMPERATURE W1 COLD)
    (SHAPE Z1 OBLONG)
    (SURFACE-CONDITION Z1 ROUGH)
    (PAINTED Z1 YELLOW)
    (HAS-HOLE Z1 TWO FRONT)
    (TEMPERATURE Z1 COLD)
    (SHAPE A2 OBLONG)
    (SURFACE-CONDITION A2 POLISHED)
    (PAINTED A2 BLUE)
    (HAS-HOLE A2 TWO FRONT)
    (TEMPERATURE A2 COLD)
    (CAN-ORIENT DRILL-PRESS BACK)
    (CAN-ORIENT PUNCH BACK)
    (CAN-ORIENT DRILL-PRESS FRONT)
    (CAN-ORIENT PUNCH FRONT)
    (HAS-PAINT IMMERSION-PAINTER YELLOW)
    (HAS-PAINT SPRAY-PAINTER YELLOW)
    (HAS-PAINT IMMERSION-PAINTER BLUE)
    (HAS-PAINT SPRAY-PAINTER BLUE)
    (HAS-PAINT IMMERSION-PAINTER BLACK)
    (HAS-PAINT SPRAY-PAINTER BLACK)
    (HAS-PAINT IMMERSION-PAINTER RED)
    (HAS-PAINT SPRAY-PAINTER RED)
    (HAS-BIT DRILL-PRESS THREE)
    (HAS-BIT PUNCH THREE)
    (HAS-BIT DRILL-PRESS TWO)
    (HAS-BIT PUNCH TWO)
    (HAS-BIT DRILL-PRESS ONE)
    (HAS-BIT PUNCH ONE)
    (PART A2)
    (PART Z1)
    (PART W1)
    (PART V1)
    (PART U1)
    (PART S1)
    (PART R1)
    (PART P1)
    (PART Q1)
    (PART O1)
    (PART N1)
    (PART M1)
    (PART L1)
    (PART K1)
    (PART J1)
    (PART I1)
    (PART H1)
    (PART G1)
    (PART F1)
    (PART E1)
    (PART D1)
    (PART C1)
    (PART B1)
    (PART A1)
    (PART Z0)
    (PART W0)
    (PART V0)
    (PART U0)
    (PART S0)
    (PART R0)
    (PART P0)
    (PART Q0)
    (PART O0)
    (PART N0)
    (PART M0)
    (PART L0)
    (PART K0)
    (PART J0)
    (PART I0)
    (PART H0)
    (PART G0)
    (PART F0)
    (PART E0)
    (PART D0)
    (PART C0)
    (PART B0)
    (PART A0)
)
(:goal (and
    (PAINTED H0 RED)
    (SHAPE D1 CYLINDRICAL)
    (PAINTED Z1 RED)
    (SHAPE B1 CYLINDRICAL)
    (SHAPE Q1 CYLINDRICAL)
    (SURFACE-CONDITION I1 ROUGH)
    (PAINTED D0 RED)
    (SURFACE-CONDITION C1 SMOOTH)
    (PAINTED P0 BLACK)
    (PAINTED C1 YELLOW)
    (SURFACE-CONDITION A1 ROUGH)
    (SURFACE-CONDITION L1 POLISHED)
    (PAINTED Z0 BLUE)
    (SHAPE P1 CYLINDRICAL)
    (SHAPE O1 CYLINDRICAL)
    (SHAPE U0 CYLINDRICAL)
    (SHAPE N0 CYLINDRICAL)
    (PAINTED C0 RED)
    (SHAPE F1 CYLINDRICAL)
    (SURFACE-CONDITION L0 SMOOTH)
    (PAINTED U0 YELLOW)
    (SURFACE-CONDITION P0 POLISHED)
    (SHAPE Z0 CYLINDRICAL)
    (SHAPE V0 CYLINDRICAL)
    (PAINTED A0 BLACK)
    (PAINTED U1 BLUE)
    (SHAPE K1 CYLINDRICAL)
    (SHAPE H1 CYLINDRICAL)
    (PAINTED K0 BLACK)
    (SURFACE-CONDITION J0 ROUGH)
    (SURFACE-CONDITION F1 ROUGH)
    (SHAPE Z1 CYLINDRICAL)
    (SHAPE Q0 CYLINDRICAL)
    (PAINTED G0 RED)
    (SHAPE M1 CYLINDRICAL)
    (SURFACE-CONDITION K0 POLISHED)
    (PAINTED S0 RED)
    (SURFACE-CONDITION M1 ROUGH)
    (PAINTED R1 YELLOW)
    (PAINTED M0 BLACK)
    (SHAPE C1 CYLINDRICAL)
    (SHAPE I0 CYLINDRICAL)
    (SURFACE-CONDITION C0 POLISHED)
    (PAINTED M1 BLACK)
    (SURFACE-CONDITION W0 SMOOTH)
    (PAINTED J1 RED)
    (SHAPE M0 CYLINDRICAL)
)))
