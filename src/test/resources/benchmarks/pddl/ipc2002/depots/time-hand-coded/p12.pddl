(define (problem depotprob9876) (:domain Depot)
(:objects
	depot0 depot1 depot2 - Depot
	distributor0 distributor1 distributor2 - Distributor
	truck0 truck1 truck2 truck3 - Truck
	pallet0 pallet1 pallet2 pallet3 pallet4 pallet5 - Pallet
	crate0 crate1 crate2 crate3 crate4 crate5 crate6 crate7 crate8 crate9 crate10 crate11 crate12 crate13 crate14 crate15 crate16 crate17 crate18 crate19 crate20 crate21 crate22 crate23 crate24 crate25 crate26 crate27 crate28 crate29 crate30 crate31 crate32 crate33 crate34 crate35 crate36 crate37 crate38 crate39 crate40 crate41 crate42 crate43 crate44 crate45 crate46 crate47 crate48 crate49 crate50 crate51 crate52 crate53 crate54 crate55 crate56 crate57 crate58 crate59 crate60 crate61 crate62 crate63 crate64 crate65 crate66 crate67 crate68 crate69 crate70 crate71 crate72 crate73 crate74 crate75 crate76 crate77 crate78 crate79 - Crate
	hoist0 hoist1 hoist2 hoist3 hoist4 hoist5 - Hoist)
(:init
	(at pallet0 depot0)
	(clear crate78)
	(at pallet1 depot1)
	(clear crate79)
	(at pallet2 depot2)
	(clear crate75)
	(at pallet3 distributor0)
	(clear crate64)
	(at pallet4 distributor1)
	(clear crate77)
	(at pallet5 distributor2)
	(clear crate73)
	(at truck0 distributor1)
	(= (speed truck0) 5)
	(at truck1 depot1)
	(= (speed truck1) 10)
	(at truck2 distributor1)
	(= (speed truck2) 4)
	(at truck3 depot2)
	(= (speed truck3) 6)
	(at hoist0 depot0)
	(available hoist0)
	(= (power hoist0) 4)
	(at hoist1 depot1)
	(available hoist1)
	(= (power hoist1) 10)
	(at hoist2 depot2)
	(available hoist2)
	(= (power hoist2) 9)
	(at hoist3 distributor0)
	(available hoist3)
	(= (power hoist3) 10)
	(at hoist4 distributor1)
	(available hoist4)
	(= (power hoist4) 1)
	(at hoist5 distributor2)
	(available hoist5)
	(= (power hoist5) 2)
	(at crate0 distributor2)
	(on crate0 pallet5)
	(= (weight crate0) 1)
	(at crate1 distributor0)
	(on crate1 pallet3)
	(= (weight crate1) 1)
	(at crate2 depot1)
	(on crate2 pallet1)
	(= (weight crate2) 1)
	(at crate3 distributor2)
	(on crate3 crate0)
	(= (weight crate3) 1)
	(at crate4 distributor2)
	(on crate4 crate3)
	(= (weight crate4) 1)
	(at crate5 distributor2)
	(on crate5 crate4)
	(= (weight crate5) 1)
	(at crate6 distributor2)
	(on crate6 crate5)
	(= (weight crate6) 1)
	(at crate7 depot1)
	(on crate7 crate2)
	(= (weight crate7) 1)
	(at crate8 distributor1)
	(on crate8 pallet4)
	(= (weight crate8) 1)
	(at crate9 depot1)
	(on crate9 crate7)
	(= (weight crate9) 1)
	(at crate10 distributor2)
	(on crate10 crate6)
	(= (weight crate10) 1)
	(at crate11 distributor1)
	(on crate11 crate8)
	(= (weight crate11) 1)
	(at crate12 distributor1)
	(on crate12 crate11)
	(= (weight crate12) 1)
	(at crate13 depot2)
	(on crate13 pallet2)
	(= (weight crate13) 1)
	(at crate14 distributor2)
	(on crate14 crate10)
	(= (weight crate14) 1)
	(at crate15 depot1)
	(on crate15 crate9)
	(= (weight crate15) 1)
	(at crate16 depot0)
	(on crate16 pallet0)
	(= (weight crate16) 1)
	(at crate17 distributor2)
	(on crate17 crate14)
	(= (weight crate17) 1)
	(at crate18 depot2)
	(on crate18 crate13)
	(= (weight crate18) 1)
	(at crate19 depot0)
	(on crate19 crate16)
	(= (weight crate19) 1)
	(at crate20 depot0)
	(on crate20 crate19)
	(= (weight crate20) 1)
	(at crate21 distributor2)
	(on crate21 crate17)
	(= (weight crate21) 1)
	(at crate22 depot2)
	(on crate22 crate18)
	(= (weight crate22) 1)
	(at crate23 distributor1)
	(on crate23 crate12)
	(= (weight crate23) 1)
	(at crate24 depot0)
	(on crate24 crate20)
	(= (weight crate24) 1)
	(at crate25 distributor2)
	(on crate25 crate21)
	(= (weight crate25) 1)
	(at crate26 depot1)
	(on crate26 crate15)
	(= (weight crate26) 1)
	(at crate27 distributor2)
	(on crate27 crate25)
	(= (weight crate27) 1)
	(at crate28 depot1)
	(on crate28 crate26)
	(= (weight crate28) 1)
	(at crate29 depot0)
	(on crate29 crate24)
	(= (weight crate29) 1)
	(at crate30 depot2)
	(on crate30 crate22)
	(= (weight crate30) 1)
	(at crate31 distributor2)
	(on crate31 crate27)
	(= (weight crate31) 1)
	(at crate32 depot0)
	(on crate32 crate29)
	(= (weight crate32) 1)
	(at crate33 distributor1)
	(on crate33 crate23)
	(= (weight crate33) 1)
	(at crate34 distributor0)
	(on crate34 crate1)
	(= (weight crate34) 1)
	(at crate35 distributor1)
	(on crate35 crate33)
	(= (weight crate35) 1)
	(at crate36 depot0)
	(on crate36 crate32)
	(= (weight crate36) 1)
	(at crate37 distributor0)
	(on crate37 crate34)
	(= (weight crate37) 1)
	(at crate38 distributor1)
	(on crate38 crate35)
	(= (weight crate38) 1)
	(at crate39 distributor0)
	(on crate39 crate37)
	(= (weight crate39) 1)
	(at crate40 depot1)
	(on crate40 crate28)
	(= (weight crate40) 1)
	(at crate41 distributor1)
	(on crate41 crate38)
	(= (weight crate41) 1)
	(at crate42 depot0)
	(on crate42 crate36)
	(= (weight crate42) 1)
	(at crate43 distributor0)
	(on crate43 crate39)
	(= (weight crate43) 1)
	(at crate44 depot1)
	(on crate44 crate40)
	(= (weight crate44) 1)
	(at crate45 depot2)
	(on crate45 crate30)
	(= (weight crate45) 1)
	(at crate46 distributor2)
	(on crate46 crate31)
	(= (weight crate46) 1)
	(at crate47 depot0)
	(on crate47 crate42)
	(= (weight crate47) 1)
	(at crate48 depot0)
	(on crate48 crate47)
	(= (weight crate48) 1)
	(at crate49 depot1)
	(on crate49 crate44)
	(= (weight crate49) 1)
	(at crate50 distributor1)
	(on crate50 crate41)
	(= (weight crate50) 1)
	(at crate51 depot1)
	(on crate51 crate49)
	(= (weight crate51) 1)
	(at crate52 distributor1)
	(on crate52 crate50)
	(= (weight crate52) 1)
	(at crate53 depot1)
	(on crate53 crate51)
	(= (weight crate53) 1)
	(at crate54 depot0)
	(on crate54 crate48)
	(= (weight crate54) 1)
	(at crate55 depot2)
	(on crate55 crate45)
	(= (weight crate55) 1)
	(at crate56 depot1)
	(on crate56 crate53)
	(= (weight crate56) 1)
	(at crate57 distributor2)
	(on crate57 crate46)
	(= (weight crate57) 1)
	(at crate58 distributor2)
	(on crate58 crate57)
	(= (weight crate58) 1)
	(at crate59 distributor1)
	(on crate59 crate52)
	(= (weight crate59) 1)
	(at crate60 depot1)
	(on crate60 crate56)
	(= (weight crate60) 1)
	(at crate61 distributor1)
	(on crate61 crate59)
	(= (weight crate61) 1)
	(at crate62 distributor0)
	(on crate62 crate43)
	(= (weight crate62) 1)
	(at crate63 distributor2)
	(on crate63 crate58)
	(= (weight crate63) 1)
	(at crate64 distributor0)
	(on crate64 crate62)
	(= (weight crate64) 1)
	(at crate65 depot1)
	(on crate65 crate60)
	(= (weight crate65) 1)
	(at crate66 depot2)
	(on crate66 crate55)
	(= (weight crate66) 1)
	(at crate67 depot1)
	(on crate67 crate65)
	(= (weight crate67) 1)
	(at crate68 depot1)
	(on crate68 crate67)
	(= (weight crate68) 1)
	(at crate69 distributor1)
	(on crate69 crate61)
	(= (weight crate69) 1)
	(at crate70 depot0)
	(on crate70 crate54)
	(= (weight crate70) 1)
	(at crate71 distributor1)
	(on crate71 crate69)
	(= (weight crate71) 1)
	(at crate72 depot2)
	(on crate72 crate66)
	(= (weight crate72) 1)
	(at crate73 distributor2)
	(on crate73 crate63)
	(= (weight crate73) 1)
	(at crate74 depot1)
	(on crate74 crate68)
	(= (weight crate74) 1)
	(at crate75 depot2)
	(on crate75 crate72)
	(= (weight crate75) 1)
	(at crate76 depot0)
	(on crate76 crate70)
	(= (weight crate76) 1)
	(at crate77 distributor1)
	(on crate77 crate71)
	(= (weight crate77) 1)
	(at crate78 depot0)
	(on crate78 crate76)
	(= (weight crate78) 1)
	(at crate79 depot1)
	(on crate79 crate74)
	(= (weight crate79) 1)
	(= (distance depot0 depot0) 0)
	(= (distance depot0 depot1) 6)
	(= (distance depot0 depot2) 5)
	(= (distance depot0 distributor0) 9)
	(= (distance depot0 distributor1) 10)
	(= (distance depot0 distributor2) 4)
	(= (distance depot1 depot0) 5)
	(= (distance depot1 depot1) 0)
	(= (distance depot1 depot2) 6)
	(= (distance depot1 distributor0) 8)
	(= (distance depot1 distributor1) 5)
	(= (distance depot1 distributor2) 5)
	(= (distance depot2 depot0) 4)
	(= (distance depot2 depot1) 4)
	(= (distance depot2 depot2) 0)
	(= (distance depot2 distributor0) 5)
	(= (distance depot2 distributor1) 3)
	(= (distance depot2 distributor2) 2)
	(= (distance distributor0 depot0) 4)
	(= (distance distributor0 depot1) 2)
	(= (distance distributor0 depot2) 5)
	(= (distance distributor0 distributor0) 0)
	(= (distance distributor0 distributor1) 1)
	(= (distance distributor0 distributor2) 6)
	(= (distance distributor1 depot0) 5)
	(= (distance distributor1 depot1) 10)
	(= (distance distributor1 depot2) 6)
	(= (distance distributor1 distributor0) 1)
	(= (distance distributor1 distributor1) 0)
	(= (distance distributor1 distributor2) 4)
	(= (distance distributor2 depot0) 10)
	(= (distance distributor2 depot1) 3)
	(= (distance distributor2 depot2) 10)
	(= (distance distributor2 distributor0) 4)
	(= (distance distributor2 distributor1) 1)
	(= (distance distributor2 distributor2) 0)
)

(:goal (and
		(on crate0 crate62)
		(on crate1 crate15)
		(on crate2 crate73)
		(on crate3 crate9)
		(on crate4 crate50)
		(on crate5 crate20)
		(on crate6 crate14)
		(on crate7 crate36)
		(on crate8 crate39)
		(on crate9 crate0)
		(on crate10 crate19)
		(on crate11 crate58)
		(on crate12 crate17)
		(on crate14 crate18)
		(on crate15 crate37)
		(on crate16 pallet4)
		(on crate17 pallet3)
		(on crate18 pallet1)
		(on crate19 crate43)
		(on crate20 crate64)
		(on crate21 crate53)
		(on crate22 crate78)
		(on crate23 crate30)
		(on crate24 crate59)
		(on crate26 crate10)
		(on crate27 crate63)
		(on crate28 crate51)
		(on crate30 crate8)
		(on crate31 crate12)
		(on crate32 crate61)
		(on crate33 pallet0)
		(on crate34 crate69)
		(on crate35 crate72)
		(on crate36 crate65)
		(on crate37 crate77)
		(on crate38 crate54)
		(on crate39 crate21)
		(on crate40 crate11)
		(on crate41 crate26)
		(on crate42 crate34)
		(on crate43 crate60)
		(on crate44 crate66)
		(on crate45 crate70)
		(on crate46 crate75)
		(on crate47 crate42)
		(on crate49 crate56)
		(on crate50 crate33)
		(on crate51 pallet5)
		(on crate52 crate16)
		(on crate53 crate38)
		(on crate54 pallet2)
		(on crate56 crate2)
		(on crate57 crate41)
		(on crate58 crate79)
		(on crate59 crate3)
		(on crate60 crate31)
		(on crate61 crate6)
		(on crate62 crate22)
		(on crate63 crate74)
		(on crate64 crate67)
		(on crate65 crate52)
		(on crate66 crate57)
		(on crate67 crate7)
		(on crate68 crate44)
		(on crate69 crate4)
		(on crate70 crate23)
		(on crate72 crate40)
		(on crate73 crate32)
		(on crate74 crate49)
		(on crate75 crate47)
		(on crate76 crate5)
		(on crate77 crate68)
		(on crate78 crate28)
		(on crate79 crate24)
	)
)

(:metric minimize (total-time)))
