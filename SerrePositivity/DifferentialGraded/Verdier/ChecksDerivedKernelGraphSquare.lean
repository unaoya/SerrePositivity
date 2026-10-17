module
public import SerrePositivity.DifferentialGraded.Verdier.DerivedKernelGraphSquare

/-! # 主導来 kernel の実際の graph 作用と商比較の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms derivedKernelGraphComparison
#print axioms derivedKernelGraph_perfect
#print axioms derivedKernelGraphPerfectFunctor
#print axioms derivedKernelGraphPerfectComparison
#print axioms derivedKernelGraphQuotientSquare
#print axioms derivedKernelQuotientPerfectHomotopyComparison
#print axioms derivedKernelLocalPerfectSquare
