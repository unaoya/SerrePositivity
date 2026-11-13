module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGClosedSlicePrismGeneral
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGClosedSlicePrismDirectNaturality
/-!
概要：Small 仮定の下で直接の前合成と従来の Yoneda 構成を比較する。
方針：全次数の鎖写像の一致から、評価関手・自然変換・全単体・slice prism の一致へ移す。
規約：従来の型・証明本文と指定された係数・時刻を保持する。
使われ方：既存の Small 版から一般対象宇宙の新入口への差し替え。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

lemma dgClosedPrecompositionDirect_eq {p q y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionDirect A D (y := y) r = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f A D r k a).symm

omit [Small.{u} D] in
lemma dgWalkingHomOriginalEvaluationDirect_eq (q y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluationDirect A D q y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluation A D q y := rfl

lemma dgWalkingHomRefinedEvaluationDirect_eq {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluationDirect A D y r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation A D y r := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluationDirect _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation
  rw [dgClosedPrecompositionDirect_eq]

lemma dgWalkingHomPrecomposeNatTransDirect_heq {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A D y r)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_hext _ _
    (dgWalkingHomRefinedEvaluationDirect_eq A D y r) rfl
  rintro ⟨x⟩
  cases x <;> rfl

lemma dgWalkingHomPrecomposeDirect_simplex_eq {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) n)
    (β : Fin (n + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A D y r).simplex s β =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r).simplex s β := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_simplex_eq_of_heq _ _
    (dgWalkingHomRefinedEvaluationDirect_eq A D y r) rfl
    (dgWalkingHomPrecomposeNatTransDirect_heq A D y r) s β

lemma dgClosedPrecompositionSlicePrismDirect_eq {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionSlicePrismDirect A D y r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionSlicePrism A D y r := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A D y r).simplex
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y).app _ s.1).val
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)) = _
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 1) => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm t)
    (dgWalkingHomPrecomposeDirect_simplex_eq A D y r _ _)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
