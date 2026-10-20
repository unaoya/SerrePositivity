module

public import SerrePositivity.InfinityCategories.F2.SimultaneousFiberDetection

/-!
概要：共通部分で底が一致する二つの有限図式を、底の円柱を保って同時に輸送する。
方針：底の図式を有限 pushout から延長し、一つの収縮の二つの制限を持ち上げる。
規約：共通部分の射に単射性を要求しない。
使われ方：積比較の単射側で、有限因子分解の共通境界を保つ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：有限 pushout は有限。
方針：有限余極限の一般補題を span に適用する。
規約：三つの対象は有限。使われ方：共通境界を貼った底の図式の収縮。 -/
lemma finite_pushout {A K L : SSet.{u}} [A.Finite] [K.Finite] [L.Finite]
    (i : A ⟶ K) (j : A ⟶ L) : (pushout i j).Finite := by
  apply SSet.finite_of_isColimit (pushoutIsPushout i j)
  rintro (_ | _ | _) <;> dsimp <;> infer_instance

/-- 概要：共通部分上の底の全円柱が一致する、二つの有限図式の共通 fiber への輸送。
方針：底の図式を pushout で貼り、一つの収縮に沿って両図式を輸送する。
規約：境界射の単射性は不要。使われ方：引き戻し内の境界の同時輸送。 -/
lemma leftFibration_glued_finite_fiber_detection {A K L E D B : SSet.{u}}
    [A.Finite] [K.Finite] [L.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q]
    (i : A ⟶ K) (j : A ⟶ L) (f : K ⟶ E) (g : L ⟶ D)
    (h : i ≫ f ≫ p = j ≫ g ≫ q) :
    ∃ b : B _⦋0⦌, ∃ s : K ⟶ vertexFiber p b, ∃ t : L ⟶ vertexFiber q b,
      ∃ Hs : SSet.Homotopy f (s ≫ vertexFiberι p b),
      ∃ Ht : SSet.Homotopy g (t ≫ vertexFiberι q b),
        (i ▷ (Δ[1] : SSet.{u})) ≫ Hs.h ≫ p =
          (j ▷ (Δ[1] : SSet.{u})) ≫ Ht.h ≫ q := by
  have := finite_pushout i j
  let d := pushout.desc (f ≫ p) (g ≫ q) h
  obtain ⟨b, ⟨H⟩⟩ := exists_nullHomotopy_of_isFilteredInfinity d
  let Hf : SSet.Homotopy (f ≫ p) (SSet.const b : K ⟶ B) := {
    h := (pushout.inl i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
    h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; exact pushout.inl_desc _ _ _
    h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
    rel := (functorHomotopyPrecomp H (pushout.inl i j)).rel }
  let Hg : SSet.Homotopy (g ≫ q) (SSet.const b : L ⟶ B) := {
    h := (pushout.inr i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
    h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; exact pushout.inr_desc _ _ _
    h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
    rel := (functorHomotopyPrecomp H (pushout.inr i j)).rel }
  obtain ⟨s, Hs, hs⟩ := leftFibration_transport_along_nullHomotopy p f b Hf
  obtain ⟨t, Ht, ht⟩ := leftFibration_transport_along_nullHomotopy q g b Hg
  refine ⟨b, s, t, Hs, Ht, ?_⟩
  rw [hs, ht]
  change (i ▷ (Δ[1] : SSet.{u})) ≫
    (pushout.inl i j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      (j ▷ (Δ[1] : SSet.{u})) ≫
        (pushout.inr i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
  rw [← Category.assoc, ← Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight,
    pushout.condition]

end SerrePositivity.InfinityCategories.F2
