(define (problem schedule-12-0)
(:domain schedule)
(:objects
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
    B0
    A0
 - part
    CIRCULAR
    OBLONG
 - ashape
    BLUE
    YELLOW
    RED
    BLACK
 - colour
    TWO
    THREE
    ONE
 - width
    BACK
    FRONT
 - anorient
)
(:init
    (SHAPE A0 CYLINDRICAL)
    (SURFACE-CONDITION A0 ROUGH)
    (PAINTED A0 BLACK)
    (HAS-HOLE A0 THREE FRONT)
    (TEMPERATURE A0 COLD)
    (SHAPE B0 CIRCULAR)
    (SURFACE-CONDITION B0 SMOOTH)
    (PAINTED B0 BLUE)
    (HAS-HOLE B0 ONE BACK)
    (TEMPERATURE B0 COLD)
    (SHAPE C0 OBLONG)
    (SURFACE-CONDITION C0 ROUGH)
    (PAINTED C0 BLUE)
    (HAS-HOLE C0 THREE FRONT)
    (TEMPERATURE C0 COLD)
    (SHAPE D0 CIRCULAR)
    (SURFACE-CONDITION D0 ROUGH)
    (PAINTED D0 YELLOW)
    (HAS-HOLE D0 ONE BACK)
    (TEMPERATURE D0 COLD)
    (SHAPE E0 CIRCULAR)
    (SURFACE-CONDITION E0 POLISHED)
    (PAINTED E0 RED)
    (HAS-HOLE E0 TWO FRONT)
    (TEMPERATURE E0 COLD)
    (SHAPE F0 OBLONG)
    (SURFACE-CONDITION F0 POLISHED)
    (PAINTED F0 YELLOW)
    (HAS-HOLE F0 ONE BACK)
    (TEMPERATURE F0 COLD)
    (SHAPE G0 OBLONG)
    (SURFACE-CONDITION G0 SMOOTH)
    (PAINTED G0 YELLOW)
    (HAS-HOLE G0 TWO FRONT)
    (TEMPERATURE G0 COLD)
    (SHAPE H0 CYLINDRICAL)
    (SURFACE-CONDITION H0 ROUGH)
    (PAINTED H0 RED)
    (HAS-HOLE H0 ONE FRONT)
    (TEMPERATURE H0 COLD)
    (SHAPE I0 CYLINDRICAL)
    (SURFACE-CONDITION I0 POLISHED)
    (PAINTED I0 BLACK)
    (HAS-HOLE I0 ONE BACK)
    (TEMPERATURE I0 COLD)
    (SHAPE J0 OBLONG)
    (SURFACE-CONDITION J0 SMOOTH)
    (PAINTED J0 YELLOW)
    (HAS-HOLE J0 ONE FRONT)
    (TEMPERATURE J0 COLD)
    (SHAPE K0 CYLINDRICAL)
    (SURFACE-CONDITION K0 ROUGH)
    (PAINTED K0 BLACK)
    (HAS-HOLE K0 THREE FRONT)
    (TEMPERATURE K0 COLD)
    (SHAPE L0 CIRCULAR)
    (SURFACE-CONDITION L0 POLISHED)
    (PAINTED L0 BLACK)
    (HAS-HOLE L0 THREE BACK)
    (TEMPERATURE L0 COLD)
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
)
(:goal (and
    (SHAPE B0 CYLINDRICAL)
    (PAINTED J0 BLUE)
    (SHAPE D0 CYLINDRICAL)
    (PAINTED L0 YELLOW)
    (PAINTED H0 YELLOW)
    (PAINTED K0 BLUE)
    (SURFACE-CONDITION J0 POLISHED)
    (PAINTED B0 YELLOW)
    (SURFACE-CONDITION A0 SMOOTH)
    (SURFACE-CONDITION F0 ROUGH)
    (SURFACE-CONDITION D0 SMOOTH)
    (PAINTED D0 BLUE)
)))
