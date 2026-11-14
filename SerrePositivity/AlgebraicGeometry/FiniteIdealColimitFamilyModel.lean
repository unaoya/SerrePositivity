module

public import SerrePositivity.AlgebraicGeometry.FiniteIdealColimitModel

/-!
概要：同じ filtered な添字に依存する有限個のイデアル模型を一つの段でそろえる。
方針：各 colimit の有限生成イデアルの模型を選び、有限個の段の上界へ移す。
規約：Stacks 0B8W (3) の有限被覆の生成元の移送。
使われ方：C03 のスキーム上の有限型イデアルの降下。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u

/-- 同じ filtered な添字の有限個の環の図式で、イデアルの模型を一つの段へそろえる。 -/
theorem exists_fg_ideal_family_model_of_isColimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    {ι : Type u} [Finite ι] (F : ι → J ⥤ CommRingCat.{u})
    (c : ∀ a, Cocone (F a)) (hc : ∀ a, IsColimit (c a))
    (I : ∀ a, Ideal (c a).pt) (hI : ∀ a, (I a).FG) :
    ∃ (j : J) (I₀ : ∀ a, Ideal ((F a).obj j)),
      (∀ a, (I₀ a).FG) ∧ ∀ a, (I₀ a).map ((c a).ι.app j).hom = I a := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose j L hL heq using fun a ↦
    exists_fg_ideal_model_of_isColimit (F a) (c a) (hc a) (I a) (hI a)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f (a : ι) : j a ⟶ k :=
    (hk (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)).some
  refine ⟨k, fun a ↦ (L a).map ((F a).map (f a)).hom, fun a ↦ (hL a).map _, ?_⟩
  intro a
  rw [Ideal.map_map, ← CommRingCat.hom_comp, (c a).w (f a)]
  exact heq a

end SerrePositivity.AlgebraicGeometry
