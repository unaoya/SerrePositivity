module
public import SerrePositivity.InfinityCategories.Derived.DGClosedSlicePrismGeneral
public import SerrePositivity.InfinityCategories.Derived.DGClosedSlicePrismDirectNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma dgClosedPrecompositionDirect_eq {p q y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    dgClosedPrecompositionDirect A D (y := y) r = dgClosedPrecomposition A D r := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (dgClosedPrecomposition_f A D r k a).symm

omit [Small.{u} D] in
lemma dgWalkingHomOriginalEvaluationDirect_eq (q y : D) :
    dgWalkingHomOriginalEvaluationDirect A D q y =
      dgWalkingHomOriginalEvaluation A D q y := rfl

lemma dgWalkingHomRefinedEvaluationDirect_eq {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    dgWalkingHomRefinedEvaluationDirect A D y r =
      dgWalkingHomRefinedEvaluation A D y r := by
  unfold dgWalkingHomRefinedEvaluationDirect dgWalkingHomRefinedEvaluation
  rw [dgClosedPrecompositionDirect_eq]

lemma dgWalkingHomPrecomposeNatTransDirect_heq {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    HEq (dgWalkingHomPrecomposeNatTransDirect A D y r)
      (dgWalkingHomPrecomposeNatTrans A D y r) := by
  apply dgStrictNatTrans_hext _ _
    (dgWalkingHomRefinedEvaluationDirect_eq A D y r) rfl
  rintro ⟨x⟩
  cases x <;> rfl

lemma dgWalkingHomPrecomposeDirect_simplex_eq {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    {n : ℕ} (s : Simplex A (DGWalkingHom.{u, v} A (homObject A D q y)) n)
    (β : Fin (n + 1) →o Fin 2) :
    (dgWalkingHomPrecomposeNatTransDirect A D y r).simplex s β =
      (dgWalkingHomPrecomposeNatTrans A D y r).simplex s β := by
  exact dgStrictNatTrans_simplex_eq_of_heq _ _
    (dgWalkingHomRefinedEvaluationDirect_eq A D y r) rfl
    (dgWalkingHomPrecomposeNatTransDirect_heq A D y r) s β

lemma dgClosedPrecompositionSlicePrismDirect_eq {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    dgClosedPrecompositionSlicePrismDirect A D y r =
      dgClosedPrecompositionSlicePrism A D y r := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
    ((dgWalkingHomPrecomposeNatTransDirect A D y r).simplex
      ((dgWalkingHomPinched A D q y).app _ s.1).val
      (pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)) = _
  exact congrArg (fun t : Simplex A D (n + 1) => (joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve A D)).symm t)
    (dgWalkingHomPrecomposeDirect_simplex_eq A D y r _ _)
end SerrePositivity.InfinityCategories
