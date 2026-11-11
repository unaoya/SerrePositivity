module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomPrismDirectNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransPinchedSlice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceOverEqualityTransport
/-!
概要：直接前合成の固定標的 slice prism と係数自然性を構成する。
方針：直接の閉前合成鎖写像と全二相単体の係数比較を使う。
規約：始域・標的の Small 仮定なしに、元の対象と全係数を保持する。
使われ方：D2 の一般対象宇宙での dg gluing 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 概要：元の pinched Hom 全体に対する、閉前合成の指定標的 slice 内の実 prism。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgClosedPrecompositionSlicePrismDirect {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y ⊗ (Δ[1] : SSet.{max u v}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y ▷ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSlice A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A D y r)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y))

/-- 概要：固定標的の等式輸送込みで、閉前合成の全 prism は dg 関手像と可換。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgClosedPrecompositionSlicePrismDirect_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (hp : (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Q.obj y))) :
    dgClosedPrecompositionSlicePrismDirect A D y r ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q) ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hp)).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map q y) ▷ (Δ[1] : SSet.{max u v})) ≫
        dgClosedPrecompositionSlicePrismDirect A E (Q.obj y) (Q.onClosed.map r) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hp)).hom.app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q)).app _
      ((dgClosedPrecompositionSlicePrismDirect A D y r).app _ s))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.roofSliceTransport_val hp]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A D y r).simplex
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y).app _ s.1).val
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q = _
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E (n + 1) => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm t)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeDirect_coefficient_naturality A D E Q y r s.1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
