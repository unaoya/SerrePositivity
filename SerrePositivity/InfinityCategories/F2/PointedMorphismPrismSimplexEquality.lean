module

public import SerrePositivity.InfinityCategories.F2.PointedMorphismPrismHead
public import SerrePositivity.InfinityCategories.F2.PointedMorphismPrismOrderedTail
public import SerrePositivity.InfinityCategories.F2.ThickeningSelfHomComparison

/-!
概要：元の二つの全係数 prism の実単体を、全 Hom で厳密に一致させる。
方針：初点の自己 Hom、head、tail を比較し、逆向きの空 Hom を元の path で検出する。
規約：元の全次数・全係数・全 path を保持。使われ方：元の実 prism 自体の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の正頂点間の全 Hom は、同じ元の二つの実単体で厳密に一致する。 -/
lemma pointedMorphismPrism_tail {K L : KanObject.{u}} (f : K ⟶ L) {n : ℕ}
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌)
    (i j : Fin (n + 1)) :
    (pointedMorphismReverseSimplex f t p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (pointedMorphismSimplex_obj f t p i.succ)
        (pointedMorphismSimplex_obj f t p j.succ)) =
    (pointedMorphismSourceSimplex f t p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  have hij := Path.le (P.obj 0)
  change i.succ ≤ j.succ at hij
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (pointedMorphismPrism_tail_of_le f t p i j (Fin.succ_le_succ_iff.mp hij)) d) P

/-- 同じ元の二つの実 prism の全単体は、元の全 Hom を保って厳密に一致する。 -/
lemma pointedMorphismPrism_simplex_eq {K L : KanObject.{u}} (f : K ⟶ L) {n : ℕ}
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌) :
    pointedMorphismReverseSimplex f t p = pointedMorphismSourceSimplex f t p := by
  refine EnrichedFunctor.ext SSet
    (fun a ↦ pointedMorphismSimplex_obj f t p a.as.down) (fun a b ↦ ?_)
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  induction a using Fin.cases <;> induction b using Fin.cases
  case zero.zero =>
    exact thickeningSelfHom_comparison (C := KanObject.{u})
      (pointedMorphismReverseSimplex f t p) (pointedMorphismSourceSimplex f t p)
      ⟨ULift.up 0⟩ (pointedMorphismSimplex_obj f t p 0)
  case zero.succ b => exact pointedMorphismPrism_head f t p b
  case succ.zero a =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change a.succ ≤ 0 at h
    simp at h
  case succ.succ a b => exact pointedMorphismPrism_tail f t p a b

end SerrePositivity.InfinityCategories.F2
