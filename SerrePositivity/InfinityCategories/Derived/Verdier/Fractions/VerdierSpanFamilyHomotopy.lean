module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanEvaluationSquare
public import SerrePositivity.KST.LocalizingInvariants.IntervalMappingFamilyTranspose

/-!
概要：実分数の全比較四角形を、パラメータ関手圏の同じ辺のホモトピーへ移す。
方針：四角形族をそのまま転置し、左右の指定経路も同じ転置で回収する。
規約：元の比較円柱を選び直さず、共通分母の始点経路を厳密に保持する。
使われ方：前段の指定分母経路と次辺比較を全関手圏で貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 同じ全四角形族を、パラメータ関手圏の下辺から上辺への元の円柱として読む。 -/
def spanSquareFamilyHomotopy {K X : SSet.{u}}
    (F : K ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) :
    SSet.Homotopy
      (internalHomFlipHomEquiv K Δ[1] X (F ≫ (pre squareBottomEdge).app X))
      (internalHomFlipHomEquiv K Δ[1] X (F ≫ (pre squareTopEdge).app X)) where
  h := internalHomFlipHomEquiv K (Δ[1] ⊗ Δ[1]) X F
  h₀ := by
    change squareBottomEdge ≫ _ = _
    exact (internalHomFlipHomEquiv_pre_app squareBottomEdge F).symm
  h₁ := by
    change squareTopEdge ≫ _ = _
    exact (internalHomFlipHomEquiv_pre_app squareTopEdge F).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

lemma spanSquareFamilyHomotopy_source {K X : SSet.{u}}
    (F : K ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
      (spanSquareFamilyHomotopy F).h = snd Δ[0] Δ[1] ≫
        internalHomFlipHomEquiv K Δ[1] X (F ≫ (pre squareLeftEdge).app X) := by
  change (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
    internalHomFlipHomEquiv K (Δ[1] ⊗ Δ[1]) X F = _
  have he : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) =
      snd Δ[0] Δ[1] ≫ squareLeftEdge := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨s, t⟩
    rw [stdSimplex_zero_eq_constant s]
    rfl
  rw [he, Category.assoc, ← internalHomFlipHomEquiv_pre_app]

lemma spanSquareFamilyHomotopy_target {K X : SSet.{u}}
    (F : K ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
      (spanSquareFamilyHomotopy F).h = snd Δ[0] Δ[1] ≫
        internalHomFlipHomEquiv K Δ[1] X (F ≫ (pre squareRightEdge).app X) := by
  change (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
    internalHomFlipHomEquiv K (Δ[1] ⊗ Δ[1]) X F = _
  have he : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) =
      snd Δ[0] Δ[1] ≫ squareRightEdge := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨s, t⟩
    rw [stdSimplex_zero_eq_constant s]
    rfl
  rw [he, Category.assoc, ← internalHomFlipHomEquiv_pre_app]

/-- 元の全正方形から作った比較辺は、パラメータ制限でも同じ一次単体を保持する。 -/
lemma spanSquareFamilyComparisonEdge_pre_parameter {P P' X : SSet.{u}} (j : P' ⟶ P)
    (F : P ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) :
    (((functorEdgeOfSimplicialHomotopy (spanSquareFamilyHomotopy F)).map ((truncation 2).map
      ((ihom (Δ[1] : SSet.{u})).map ((pre j).app X)))).edge) =
      (functorEdgeOfSimplicialHomotopy (spanSquareFamilyHomotopy (j ≫ F))).edge := by
  change ((ihom (Δ[1] : SSet.{u})).map ((pre j).app X)).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (curry (spanSquareFamilyHomotopy F).h)) = _
  rw [← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  rw [← curry_natural_right]
  apply congrArg curry
  exact (internalHomFlipHomEquiv_pre j F).symm

/-- 実分母の元の辺図式を、商後合成した同じ一単体。 -/
def verdierSpanDenominatorDiagram {A B C : StableCategory.{u}}
    (i : ExactMap A B) (q : ExactMap B C) (x : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) : (Δ[1] : SSet.{u}) ⟶ C.obj :=
  (joinStdSimplexIso 0 0).inv ≫ d.val.val ≫ q.hom

/-- 次辺の商比較の始点経路は、同じ共通実分母を定値関手へ写した経路そのもの。 -/
lemma verdierSpanFamilyHomotopy_source
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) {K : SSet.{u}}
    (g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i x y) d) :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
      (spanSquareFamilyHomotopy (g ≫ vertexFiberι
        (verdierDenominatorSpanProjection i x y) d ≫ verdierSpanEvaluationSquare h x y)).h =
    snd Δ[0] Δ[1] ≫ verdierSpanDenominatorDiagram i q x d ≫ curry (snd K C.obj) := by
  rw [spanSquareFamilyHomotopy_source]
  have hc : ((verdierDenominatorOver i x).ι ≫
      F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x) ≫
      (ihom (Δ[1] : SSet.{u})).map q.hom).app (Opposite.op ⦋0⦌) d =
      functorVertex (verdierSpanDenominatorDiagram i q x d) := by
    change ((ihom (Δ[1] : SSet.{u})).map q.hom).app (Opposite.op ⦋0⦌)
      ((F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x)).app
        (Opposite.op ⦋0⦌) d.val) = _
    rw [F2.Idempotent.pointSliceArrowMap_vertex]
    rfl
  have he := congrArg (fun f => g ≫ f) (verdierSpanEvaluationSquare_fiber_left h x y d)
  simp only [SSet.comp_const, hc] at he
  simp only [Category.assoc]
  rw [he, spanInternalHomFlip_const]

end SerrePositivity.KST.LocalizingInvariants
