module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.GluedFiberDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredNullHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationHomotopyTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.MappedBoundaryFiberTransport

/-!
概要：共通の元の境界と二つの有限模型を、同じ fiber へ全円柱を保って輸送する。
方針：底を有限 pushout で貼り、境界を先に輸送してから両模型へ相対延長する。
規約：境界の像の円柱を厳密に保持。使われ方：任意の Kan 二入力の相対有限検出。

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

/-- 概要：共通の境界の輸送を保つ、二つの有限模型の同時輸送。
方針：一つの底収縮と境界輸送の二つの相対延長。
規約：元の境界の全円柱。使われ方：標的二入力を元の二入力へ移す。 -/
lemma leftFibration_glued_mapped_boundary_transport {A K L R E D B : SSet.{u}}
    [A.Finite] [K.Finite] [L.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : R ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (r : D ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r] (c : R ⟶ E) (d : R ⟶ D)
    (hc : c ≫ q = p) (hd : d ≫ r = p)
    (i : A ⟶ K) [Mono i] (j : A ⟶ L) [Mono j]
    (a : A ⟶ R) (f : K ⟶ E) (g : L ⟶ D)
    (hf : i ≫ f = a ≫ c) (hg : j ≫ g = a ≫ d) :
    ∃ b : B _⦋0⦌, ∃ t : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b,
      ∃ s : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b, ∃ v : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r b,
      i ≫ s = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b ∧
      j ≫ v = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p r d hd b ∧
      ∃ T : SSet.Homotopy a (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b),
      ∃ U : SSet.Homotopy f (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b),
      ∃ V : SSet.Homotopy g (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r b),
        (i ▷ (Δ[1] : SSet.{u})) ≫ U.h = T.h ≫ c ∧
        (j ▷ (Δ[1] : SSet.{u})) ≫ V.h = T.h ≫ d := by
  have hb : i ≫ f ≫ q = j ≫ g ≫ r := by
    rw [← Category.assoc, hf, Category.assoc, hc,
      ← Category.assoc, hg, Category.assoc, hd]
  have := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finite_pushout i j
  let e := pushout.desc (f ≫ q) (g ≫ r) hb
  obtain ⟨b, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_nullHomotopy_of_isFilteredInfinity e
  let Hf : SSet.Homotopy (f ≫ q) (SSet.const b : K ⟶ B) :=
    { h := (pushout.inl i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; exact pushout.inl_desc _ _ _
      h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
      rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (pushout.inl i j)).rel }
  let Hg : SSet.Homotopy (g ≫ r) (SSet.const b : L ⟶ B) :=
    { h := (pushout.inr i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; exact pushout.inr_desc _ _ _
      h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
      rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (pushout.inr i j)).rel }
  let Ha : SSet.Homotopy (a ≫ p) (SSet.const b : A ⟶ B) :=
    { h := (i ▷ (Δ[1] : SSet.{u})) ≫ Hf.h
      h₀ := by
        change SSet.ι₀ ≫ (i ▷ (Δ[1] : SSet.{u})) ≫ Hf.h = a ≫ p
        rw [SSet.ι₀_comp_assoc, Hf.h₀, ← Category.assoc, hf, Category.assoc, hc]
      h₁ := by
        change SSet.ι₁ ≫ (i ▷ (Δ[1] : SSet.{u})) ≫ Hf.h = SSet.const b
        rw [SSet.ι₁_comp_assoc, Hf.h₁, SSet.comp_const]
      rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Hf i).rel }
  obtain ⟨t, T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_transport_along_nullHomotopy p a b Ha
  obtain ⟨s, hs, U, hU, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.leftFibration_transport_mapped_boundary
    p q c hc i a f hf b Hf t T hT
  have hT' : T.h ≫ p = (j ▷ (Δ[1] : SSet.{u})) ≫ Hg.h := by
    rw [hT]
    change (i ▷ (Δ[1] : SSet.{u})) ≫
      (pushout.inl i j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        (j ▷ (Δ[1] : SSet.{u})) ≫ (pushout.inr i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
    rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, pushout.condition]
  obtain ⟨v, hv, V, hV, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.leftFibration_transport_mapped_boundary
    p r d hd j a g hg b Hg t T hT'
  exact ⟨b, t, s, v, hs, hv, T, U, V, hU, hV⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
