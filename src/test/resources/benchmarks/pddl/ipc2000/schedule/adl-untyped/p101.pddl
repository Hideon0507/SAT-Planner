(define (problem schedule-35-1)
(:domain schedule)
(:objects
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
    (PAINTED A0 YELLOW)
    (HAS-HOLE A0 ONE FRONT)
    (TEMPERATURE A0 COLD)
    (SHAPE B0 CIRCULAR)
    (SURFACE-CONDITION B0 SMOOTH)
    (PAINTED B0 RED)
    (HAS-HOLE B0 ONE BACK)
    (TEMPERATURE B0 COLD)
    (SHAPE C0 CIRCULAR)
    (SURFACE-CONDITION C0 ROUGH)
    (PAINTED C0 RED)
    (HAS-HOLE C0 THREE BACK)
    (TEMPERATURE C0 COLD)
    (SHAPE D0 CYLINDRICAL)
    (SURFACE-CONDITION D0 SMOOTH)
    (PAINTED D0 RED)
    (HAS-HOLE D0 THREE BACK)
    (TEMPERATURE D0 COLD)
    (SHAPE E0 OBLONG)
    (SURFACE-CONDITION E0 ROUGH)
    (PAINTED E0 RED)
    (HAS-HOLE E0 TWO BACK)
    (TEMPERATURE E0 COLD)
    (SHAPE F0 OBLONG)
    (SURFACE-CONDITION F0 POLISHED)
    (PAINTED F0 BLACK)
    (HAS-HOLE F0 ONE BACK)
    (TEMPERATURE F0 COLD)
    (SHAPE G0 CIRCULAR)
    (SURFACE-CONDITION G0 SMOOTH)
    (PAINTED G0 YELLOW)
    (HAS-HOLE G0 ONE BACK)
    (TEMPERATURE G0 COLD)
    (SHAPE H0 OBLONG)
    (SURFACE-CONDITION H0 ROUGH)
    (PAINTED H0 YELLOW)
    (HAS-HOLE H0 TWO FRONT)
    (TEMPERATURE H0 COLD)
    (SHAPE I0 OBLONG)
    (SURFACE-CONDITION I0 SMOOTH)
    (PAINTED I0 BLACK)
    (HAS-HOLE I0 ONE FRONT)
    (TEMPERATURE I0 COLD)
    (SHAPE J0 OBLONG)
    (SURFACE-CONDITION J0 SMOOTH)
    (PAINTED J0 YELLOW)
    (HAS-HOLE J0 TWO BACK)
    (TEMPERATURE J0 COLD)
    (SHAPE K0 CIRCULAR)
    (SURFACE-CONDITION K0 SMOOTH)
    (PAINTED K0 BLACK)
    (HAS-HOLE K0 THREE BACK)
    (TEMPERATURE K0 COLD)
    (SHAPE L0 OBLONG)
    (SURFACE-CONDITION L0 POLISHED)
    (PAINTED L0 BLACK)
    (HAS-HOLE L0 TWO BACK)
    (TEMPERATURE L0 COLD)
    (SHAPE M0 CIRCULAR)
    (SURFACE-CONDITION M0 POLISHED)
    (PAINTED M0 RED)
    (HAS-HOLE M0 THREE FRONT)
    (TEMPERATURE M0 COLD)
    (SHAPE N0 OBLONG)
    (SURFACE-CONDITION N0 ROUGH)
    (PAINTED N0 YELLOW)
    (HAS-HOLE N0 ONE FRONT)
    (TEMPERATURE N0 COLD)
    (SHAPE O0 OBLONG)
    (SURFACE-CONDITION O0 SMOOTH)
    (PAINTED O0 YELLOW)
    (HAS-HOLE O0 TWO FRONT)
    (TEMPERATURE O0 COLD)
    (SHAPE Q0 OBLONG)
    (SURFACE-CONDITION Q0 POLISHED)
    (PAINTED Q0 BLUE)
    (HAS-HOLE Q0 ONE FRONT)
    (TEMPERATURE Q0 COLD)
    (SHAPE P0 CIRCULAR)
    (SURFACE-CONDITION P0 SMOOTH)
    (PAINTED P0 YELLOW)
    (HAS-HOLE P0 ONE FRONT)
    (TEMPERATURE P0 COLD)
    (SHAPE R0 CYLINDRICAL)
    (SURFACE-CONDITION R0 SMOOTH)
    (PAINTED R0 BLACK)
    (HAS-HOLE R0 ONE FRONT)
    (TEMPERATURE R0 COLD)
    (SHAPE S0 CYLINDRICAL)
    (SURFACE-CONDITION S0 SMOOTH)
    (PAINTED S0 BLACK)
    (HAS-HOLE S0 ONE FRONT)
    (TEMPERATURE S0 COLD)
    (SHAPE U0 OBLONG)
    (SURFACE-CONDITION U0 ROUGH)
    (PAINTED U0 BLACK)
    (HAS-HOLE U0 TWO BACK)
    (TEMPERATURE U0 COLD)
    (SHAPE V0 CYLINDRICAL)
    (SURFACE-CONDITION V0 ROUGH)
    (PAINTED V0 BLACK)
    (HAS-HOLE V0 TWO FRONT)
    (TEMPERATURE V0 COLD)
    (SHAPE W0 CYLINDRICAL)
    (SURFACE-CONDITION W0 ROUGH)
    (PAINTED W0 BLUE)
    (HAS-HOLE W0 TWO BACK)
    (TEMPERATURE W0 COLD)
    (SHAPE Z0 CYLINDRICAL)
    (SURFACE-CONDITION Z0 ROUGH)
    (PAINTED Z0 BLUE)
    (HAS-HOLE Z0 ONE FRONT)
    (TEMPERATURE Z0 COLD)
    (SHAPE A1 OBLONG)
    (SURFACE-CONDITION A1 POLISHED)
    (PAINTED A1 BLUE)
    (HAS-HOLE A1 ONE BACK)
    (TEMPERATURE A1 COLD)
    (SHAPE B1 OBLONG)
    (SURFACE-CONDITION B1 ROUGH)
    (PAINTED B1 BLUE)
    (HAS-HOLE B1 ONE BACK)
    (TEMPERATURE B1 COLD)
    (SHAPE C1 CYLINDRICAL)
    (SURFACE-CONDITION C1 ROUGH)
    (PAINTED C1 RED)
    (HAS-HOLE C1 TWO BACK)
    (TEMPERATURE C1 COLD)
    (SHAPE D1 CIRCULAR)
    (SURFACE-CONDITION D1 POLISHED)
    (PAINTED D1 YELLOW)
    (HAS-HOLE D1 ONE BACK)
    (TEMPERATURE D1 COLD)
    (SHAPE E1 OBLONG)
    (SURFACE-CONDITION E1 SMOOTH)
    (PAINTED E1 BLACK)
    (HAS-HOLE E1 THREE FRONT)
    (TEMPERATURE E1 COLD)
    (SHAPE F1 CIRCULAR)
    (SURFACE-CONDITION F1 POLISHED)
    (PAINTED F1 BLACK)
    (HAS-HOLE F1 THREE FRONT)
    (TEMPERATURE F1 COLD)
    (SHAPE G1 CYLINDRICAL)
    (SURFACE-CONDITION G1 ROUGH)
    (PAINTED G1 BLUE)
    (HAS-HOLE G1 THREE FRONT)
    (TEMPERATURE G1 COLD)
    (SHAPE H1 OBLONG)
    (SURFACE-CONDITION H1 ROUGH)
    (PAINTED H1 BLACK)
    (HAS-HOLE H1 TWO BACK)
    (TEMPERATURE H1 COLD)
    (SHAPE I1 CYLINDRICAL)
    (SURFACE-CONDITION I1 ROUGH)
    (PAINTED I1 BLUE)
    (HAS-HOLE I1 ONE FRONT)
    (TEMPERATURE I1 COLD)
    (SHAPE J1 CIRCULAR)
    (SURFACE-CONDITION J1 SMOOTH)
    (PAINTED J1 YELLOW)
    (HAS-HOLE J1 ONE FRONT)
    (TEMPERATURE J1 COLD)
    (SHAPE K1 CIRCULAR)
    (SURFACE-CONDITION K1 ROUGH)
    (PAINTED K1 RED)
    (HAS-HOLE K1 TWO BACK)
    (TEMPERATURE K1 COLD)
    (SHAPE L1 CIRCULAR)
    (SURFACE-CONDITION L1 SMOOTH)
    (PAINTED L1 YELLOW)
    (HAS-HOLE L1 THREE FRONT)
    (TEMPERATURE L1 COLD)
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
    (SHAPE K0 CYLINDRICAL)
    (PAINTED H1 YELLOW)
    (SHAPE D1 CYLINDRICAL)
    (SURFACE-CONDITION N0 POLISHED)
    (SHAPE N0 CYLINDRICAL)
    (PAINTED O0 BLACK)
    (SURFACE-CONDITION L0 SMOOTH)
    (SHAPE M0 CYLINDRICAL)
    (SURFACE-CONDITION D1 ROUGH)
    (SURFACE-CONDITION K1 POLISHED)
    (PAINTED U0 RED)
    (PAINTED I1 YELLOW)
    (SHAPE B1 CYLINDRICAL)
    (PAINTED R0 BLUE)
    (SURFACE-CONDITION D0 ROUGH)
    (PAINTED K1 YELLOW)
    (SHAPE A0 CYLINDRICAL)
    (SURFACE-CONDITION B0 ROUGH)
    (SHAPE G0 CYLINDRICAL)
    (SURFACE-CONDITION H1 POLISHED)
    (PAINTED G0 BLACK)
    (PAINTED A0 BLUE)
    (SHAPE I0 CYLINDRICAL)
    (SURFACE-CONDITION V0 SMOOTH)
    (SURFACE-CONDITION I1 SMOOTH)
    (SURFACE-CONDITION B1 POLISHED)
    (PAINTED A1 RED)
    (SURFACE-CONDITION C0 SMOOTH)
    (SURFACE-CONDITION O0 ROUGH)
    (SURFACE-CONDITION J0 POLISHED)
    (SHAPE F0 CYLINDRICAL)
    (SURFACE-CONDITION K0 POLISHED)
    (SHAPE Q0 CYLINDRICAL)
    (PAINTED Q0 BLACK)
    (PAINTED L1 BLUE)
)))
