import Exp7GRHBridge.Global

#check Exp7.GRHIntegration.primeConductor
#print axioms Exp7.GRHIntegration.primeConductor
#check Exp7.searchHigh
#print axioms Exp7.searchHigh
#check Exp7.searchLow
#print axioms Exp7.searchLow
#check Exp7.GRHIntegration.excludes_above_bridge
#print axioms Exp7.GRHIntegration.excludes_above_bridge
#check Exp7.GRHIntegration.theoremD_global
#print axioms Exp7.GRHIntegration.theoremD_global
#check Exp7.GRHIntegration.theoremD_fundamental_global
#print axioms Exp7.GRHIntegration.theoremD_fundamental_global

example : Exp7.known.length = 33 ∧ Exp7.known.Nodup := by decide
