module

public import SerrePositivity.InfinityCategories.F1.CoherentEdges

/-!
概要：三つの通常射の coherent 三単体の四面を、元の標準合成三角形と同定する。
方針：通常の nerve の四面を計算し、標準射の単体的自然性で移す。
規約：合成三角形を選び直さない。使われ方：全 h Fun の合成比較の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CoherentComposition

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)

def tetrahedron : SimplicialNerve C _⦋3⦌ :=
  (nerveToCoherent C).app (Opposite.op ⦋3⦌) (ComposableArrows.mk₃ a b c)

lemma face_last : (SimplicialNerve C).δ 3 (tetrahedron a b c) =
    (coherentNerveCompStruct a b).simplex := by
  change (SimplicialNerve C).δ 3
    ((nerveToCoherent C).app _ (ComposableArrows.mk₃ a b c)) = _
  rw [← δ_naturality_apply]
  apply congrArg ((nerveToCoherent C).app (Opposite.op ⦋2⦌))
  exact ComposableArrows.ext₂ rfl rfl rfl (by simp; rfl) (by simp; rfl)

lemma face_first : (SimplicialNerve C).δ 0 (tetrahedron a b c) =
    (coherentNerveCompStruct b c).simplex := by
  change (SimplicialNerve C).δ 0
    ((nerveToCoherent C).app _ (ComposableArrows.mk₃ a b c)) = _
  rw [← δ_naturality_apply]
  apply congrArg ((nerveToCoherent C).app (Opposite.op ⦋2⦌))
  exact ComposableArrows.ext₂ rfl rfl rfl (by simp; rfl) (by simp; rfl)

lemma face_lower : (SimplicialNerve C).δ 1 (tetrahedron a b c) =
    (coherentNerveCompStruct (a ≫ b) c).simplex := by
  change (SimplicialNerve C).δ 1
    ((nerveToCoherent C).app _ (ComposableArrows.mk₃ a b c)) = _
  rw [← δ_naturality_apply]
  apply congrArg ((nerveToCoherent C).app (Opposite.op ⦋2⦌))
  exact ComposableArrows.ext₂ rfl rfl rfl (by simp; rfl) (by simp; rfl)

lemma face_upper : (SimplicialNerve C).δ 2 (tetrahedron a b c) =
    (coherentNerveCompStruct a (b ≫ c)).simplex := by
  change (SimplicialNerve C).δ 2
    ((nerveToCoherent C).app _ (ComposableArrows.mk₃ a b c)) = _
  rw [← δ_naturality_apply]
  apply congrArg ((nerveToCoherent C).app (Opposite.op ⦋2⦌))
  exact ComposableArrows.ext₂ rfl rfl rfl (by simp; rfl) (by simp; rfl)

lemma face_map {i : Fin 4} {s : SimplicialNerve C _⦋2⦌}
    (h : (SimplicialNerve C).δ i (tetrahedron a b c) = s) :
    stdSimplex.δ i ≫ SSet.yonedaEquiv.symm (tetrahedron a b c) =
      SSet.yonedaEquiv.symm s := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

end SerrePositivity.KST.LocalizingInvariants.CoherentComposition
