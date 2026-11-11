module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.GluedFiberDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredNullHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationHomotopyTransport


/-!
概要：共通部分で底が一致する二つの有限図式を、底の円柱を保って同時に輸送する。
方針：底の図式を有限 pushout から延長し、一つの収縮の二つの制限を持ち上げる。
規約：共通部分の射に単射性を要求しない。
使われ方：積比較の単射側で、有限因子分解の共通境界を保つ。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：共通部分上の底の全円柱が一致する、二つの有限図式の共通 fiber への輸送。
方針：底の図式を pushout で貼り、一つの収縮に沿って両図式を輸送する。
規約：境界射の単射性は不要。使われ方：引き戻し内の境界の同時輸送。 -/
lemma leftFibration_glued_finite_fiber_detection {A K L E D B : SSet.{u}}
    [A.Finite] [K.Finite] [L.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : D ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (i : A ⟶ K) (j : A ⟶ L) (f : K ⟶ E) (g : L ⟶ D)
    (h : i ≫ f ≫ p = j ≫ g ≫ q) :
    ∃ b : B _⦋0⦌, ∃ s : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b, ∃ t : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b,
      ∃ Hs : SSet.Homotopy f (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b),
      ∃ Ht : SSet.Homotopy g (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b),
        (i ▷ (Δ[1] : SSet.{u})) ≫ Hs.h ≫ p =
          (j ▷ (Δ[1] : SSet.{u})) ≫ Ht.h ≫ q := by
  have := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finite_pushout i j
  let d := pushout.desc (f ≫ p) (g ≫ q) h
  obtain ⟨b, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_nullHomotopy_of_isFilteredInfinity d
  let Hf : SSet.Homotopy (f ≫ p) (SSet.const b : K ⟶ B) := {
    h := (pushout.inl i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
    h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; exact pushout.inl_desc _ _ _
    h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
    rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (pushout.inl i j)).rel }
  let Hg : SSet.Homotopy (g ≫ q) (SSet.const b : L ⟶ B) := {
    h := (pushout.inr i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
    h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; exact pushout.inr_desc _ _ _
    h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
    rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (pushout.inr i j)).rel }
  obtain ⟨s, Hs, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_transport_along_nullHomotopy p f b Hf
  obtain ⟨t, Ht, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_transport_along_nullHomotopy q g b Hg
  refine ⟨b, s, t, Hs, Ht, ?_⟩
  rw [hs, ht]
  change (i ▷ (Δ[1] : SSet.{u})) ≫
    (pushout.inl i j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      (j ▷ (Δ[1] : SSet.{u})) ≫
        (pushout.inr i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
  rw [← Category.assoc, ← Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight,
    pushout.condition]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
