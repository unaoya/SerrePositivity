module
public import SerrePositivity.KST.NonConnective.DGKappaSplitCofiberFamily
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionExact

/-!
概要：元の全 cofiber 図式族の四つの評価を、元の厳密 dg 作用へ戻す。
方針：同じ二変数作用の転置と頂点評価を使い、全単体上の射として比較する。
規約：D-12 の明示入力と元の四辺・二胞体を保持する。
使われ方：連結 K の実加法性を同じ cone 上の swindle に適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

private lemma transpose_evaluate {A B P : SSet.{u}} (F : P ⟶ (ihom A).obj B)
    (p : P _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B).symm (F.app (Opposite.op ⦋0⦌) p) := by
  change curry ((β_ P A).hom ≫ uncurry F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.curry_evaluation_vertex]
  have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.curry_vertex_evaluation (uncurry F) p
  rw [curry_uncurry] at he
  rw [he]
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B) (lift (𝟙 A) (SSet.const p) ≫ uncurry F))
  rw [Equiv.symm_apply_apply]
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)
  (H : ∀ X : PresentedPerfectDGObject R (DGKappaCone R D I), DGKappaSplitCofiberInput R D I X)

/-- 同じ全 cofiber 族の各角での評価は、元の全関手四角形の同じ角を回収する。 -/
theorem dgKappaSplitCofiberFamily_evaluate (i j : Fin 2) :
    (dgKappaSplitCofiberFamily R D I Z H ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaSplitPerfFamilySquare R D I Z) i j) := by
  rw [dgKappaSplitCofiberFamily_ι]
  exact transpose_evaluate _ _

/-- 元の下側二胞体の全三頂点は、同じ閉関手の全 native 作用の頂点。 -/
theorem dgKappaSplitPerfFamilySquare_lower_vertex (i : Fin 3) :
    (dgKappaSplitPerfFamilySquare R D I Z).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i)) =
      (dgKappaFullPerfFamilyMap R D I).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) ((dgKappaSplitClosedLower R D I).obj i)))) := by
  have hv := congrArg (fun F => F.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm i)) (dgKappaSplitPerfFamilySquare_lower R D I Z)
  refine hv.trans (congrArg ((dgKappaFullPerfFamilyMap R D I).app (Opposite.op ⦋0⦌)) ?_)
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- 元の cofiber 族の subobject 評価は、同じ恒等 dg 入力の全 Perf 作用。 -/
theorem dgKappaSplitCofiberFamily_subobject :
    (dgKappaSplitCofiberFamily R D I Z H ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (A := R) (DGKappaCone R D I))) := by
  rw [dgKappaSplitCofiberFamily_evaluate]
  have hv := dgKappaSplitPerfFamilySquare_lower_vertex R D I Z 0
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaSplitPerfFamilySquare R D I Z) 0 0 = _ at hv
  rw [hv, dgKappaFullPerfFamilyMap_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

/-- 元の cofiber 族の middle 評価は、同じ id ⊕ T の全 Perf 作用。 -/
theorem dgKappaSplitCofiberFamily_middle :
    (dgKappaSplitCofiberFamily R D I Z H ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaSwindleSource R D I)) := by
  rw [dgKappaSplitCofiberFamily_evaluate]
  have hv := dgKappaSplitPerfFamilySquare_lower_vertex R D I Z 1
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaSplitPerfFamilySquare R D I Z) 1 0 = _ at hv
  rw [hv, dgKappaFullPerfFamilyMap_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

/-- 元の cofiber 族の quotient 評価は、同じ可算和 T の全 Perf 作用。 -/
theorem dgKappaSplitCofiberFamily_quotient :
    (dgKappaSplitCofiberFamily R D I Z H ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaConeCountableSum R D I)) := by
  rw [dgKappaSplitCofiberFamily_evaluate]
  have hv := dgKappaSplitPerfFamilySquare_lower_vertex R D I Z 2
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaSplitPerfFamilySquare R D I Z) 1 1 = _ at hv
  rw [hv, dgKappaFullPerfFamilyMap_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

/-- 元の cofiber 族の零角評価は、同じ実零自己関手の全 Perf 作用。 -/
theorem dgKappaSplitCofiberFamily_zero :
    (dgKappaSplitCofiberFamily R D I Z H ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaZeroFunctor R D I Z)) := by
  rw [dgKappaSplitCofiberFamily_evaluate, dgKappaSplitPerfFamilySquare_corner,
    dgKappaFullPerfFamilyMap_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

end SerrePositivity.KST.NonConnective
