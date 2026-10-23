module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiniteCellShapes
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits

/-!
概要：空形状・標準単体・有限和・単射側のある pushout から全有限形状へ帰納する。
方針：次元の強帰納と骨格の帰納を組み合わせ、実際の有限な相対セル付着を使う。
規約：元の有限形状を保持。使われ方：coherent filtered 余極限の有限極限交換への帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 有限形状の性質は空形状・単体・有限和・単射側のある接着から帰納できる。 -/
lemma finiteShape_cell_induction (P : SSet.{u} → Prop)
    (hIso : ∀ {A B : SSet.{u}}, (A ≅ B) → P A → P B)
    (hEmpty : ∀ X : SSet.{u}, P (⊥ : X.Subcomplex))
    (hSimplex : ∀ n : ℕ, P (Δ[n] : SSet.{u}))
    (hSum : ∀ {ι : Type u} [Finite ι] (F : ι → SSet.{u}),
      (∀ i, P (F i)) → P (∐ F))
    (hPushout : ∀ {A B C D : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
      {i : B ⟶ D} {j : C ⟶ D} [Mono g], IsPushout f g i j → P A → P B → P C → P D)
    (X : SSet.{u}) [X.Finite] : P X := by
  have hdim : ∀ d (Y : SSet.{u}) [Y.Finite] [Y.HasDimensionLT d], P Y := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Y hfin hdim
      let e := (⊥ : Y.Subcomplex).ι
      have hs : ∀ n, n ≤ d → P (SSet.skeletonOfMono e n) := by
        intro n
        induction n with
        | zero =>
          intro hn
          simpa only [SSet.skeletonOfMono_zero, e, Subfunctor.range_ι] using hEmpty Y
        | succ n hn =>
          intro hnd
          have hb : P (∂Δ[n] : SSet.{u}) :=
            ih n (Nat.lt_of_succ_le hnd) _
          have hbd := hSum
            (fun _ : SSet.relativeCellComplexOfMono.Cell e n => (∂Δ[n] : SSet.{u}))
            (fun _ => hb)
          have hsd := hSum
            (fun _ : SSet.relativeCellComplexOfMono.Cell e n => (Δ[n] : SSet.{u}))
            (fun _ => hSimplex n)
          have : Mono (SSet.relativeCellComplexOfMono.l e n) := finiteCellShapeAttachment_mono e n
          exact hPushout (SSet.relativeCellComplexOfMono.isPushout e n) hbd
            (hn (Nat.le_of_succ_le hnd)) hsd
      have htop : SSet.skeletonOfMono e d = ⊤ := by
        simp only [SSet.skeletonOfMono, OrderHom.coe_mk,
          skeleton_eq_top_of_dimension Y d, sup_top_eq]
      have hP := hs d le_rfl
      rw [htop] at hP
      exact hIso (Subcomplex.topIso Y) hP
  obtain ⟨d, hd⟩ := X.hasDimensionLT_of_finite
  exact hdim d X

end SerrePositivity.InfinityCategories.F2
