module

public import SerrePositivity.KST.LocalizingInvariants.RelativeTerminalPullbackFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-!
概要：実 pullback 族の両端を同じ区間境界上で固定し、元の二脚を保って同時延長する。
方針：両端点図式の自然性と区間境界包含の単射性から、元の相対 corner の RLP を適用する。
規約：始端・終端を別々の充填で選ばない。元の cospan・終端列を同時に保持する。
使われ方：実分数の回収円柱の両境界を同じ前段輸送へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma spanIntervalBoundaryDiagram_post {S X Y : SSet.{u}} (f g : S ⟶ X) (p : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (f ≫ p) (g ≫ p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  change p.app _ (if s.val 0 = 0 then f.app _ x else g.app _ x) =
    (if s.val 0 = 0 then p.app _ (f.app _ x) else p.app _ (g.app _ x))
  split_ifs <;> rfl

/-- 区間の両端を同じパラメータ円柱の境界へ含める元の射。 -/
def spanIntervalBoundaryMap (S : SSet.{u}) :
    (boundary 1 : SSet.{u}) ⊗ S ⟶ S ⊗ (Δ[1] : SSet.{u}) :=
  ((boundary 1).ι ▷ S) ≫ (β_ (Δ[1] : SSet.{u}) S).hom

instance spanIntervalBoundaryMap_mono (S : SSet.{u}) : Mono (spanIntervalBoundaryMap S) := by
  have : Mono ((boundary 1).ι ▷ S) := (tensorRight S).map_mono _
  unfold spanIntervalBoundaryMap
  infer_instance

lemma spanIntervalBoundaryMap_zero (S : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 S ≫ spanIntervalBoundaryMap S =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) := by
  rw [spanIntervalBoundaryMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι]
  rfl

lemma spanIntervalBoundaryMap_one (S : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 S ≫ spanIntervalBoundaryMap S =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) := by
  rw [spanIntervalBoundaryMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι]
  rfl

/-- 同じ円柱の両端の図式を、元の境界制限として厳密に回収する。 -/
lemma spanIntervalBoundaryDiagram_of_endpoints {S Y : SSet.{u}}
    (H : S ⊗ (Δ[1] : SSet.{u}) ⟶ Y) (f g : S ⟶ Y)
    (hf : f = (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ H)
    (hg : g = (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g = spanIntervalBoundaryMap S ≫ H := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict ((β_ (Δ[1] : SSet.{u}) S).hom ≫ H)
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 S ≫ (β_ (Δ[1] : SSet.{u}) S).hom =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) := rfl
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S ≫ (β_ (Δ[1] : SSet.{u}) S).hom =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) := rfl
  rw [hf, hg]
  simpa only [spanIntervalBoundaryMap, ← Category.assoc, h₀, h₁] using h.symm

/-- 元の両端補完を、一つの相対充填で固定し cospan と終端列も同時に保つ。 -/
lemma exists_twoEndpoint_terminalPullbackFamily {S X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (n : ℕ)
    (G : S ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (F₀ F₁ : S ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (h₀p : F₀ ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ G ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))
    (h₁p : F₁ ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ G ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))
    (h₀t : F₀ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ G ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X))
    (h₁t : F₁ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ G ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X)) :
    ∃ F : S ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X),
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ F = F₀ ∧
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ F = F₁ ∧
      F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
        G ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) ∧
      F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) =
        G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) := by
  let j := spanIntervalBoundaryMap S
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram F₀ F₁
  let b := G ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X)
  let c := G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X)
  have hab : a ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) = j ≫ b := by
    dsimp only [a]
    rw [spanIntervalBoundaryDiagram_post]
    exact spanIntervalBoundaryDiagram_of_endpoints b _ _ h₀p h₁p
  have hac : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) = j ≫ c := by
    dsimp only [a]
    rw [spanIntervalBoundaryDiagram_post]
    exact spanIntervalBoundaryDiagram_of_endpoints c _ _ h₀t h₁t
  have hbc : c ≫ (ihom (Δ[0] : SSet.{u})).map (pullbackProjection X) =
      b ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app ((ihom (horn 2 2 : SSet.{u})).obj X) := by
    dsimp only [c, b]
    rw [Category.assoc, Category.assoc, ← (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).naturality]
  obtain ⟨F, hjF, hFp, hFt⟩ := exists_relative_terminalPullbackFamily n j a b c hab hac hbc
  have h₀ := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 S ≫ f) hjF
  have h₁ := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 S ≫ f) hjF
  rw [← Category.assoc, spanIntervalBoundaryMap_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero] at h₀
  rw [← Category.assoc, spanIntervalBoundaryMap_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one] at h₁
  exact ⟨F, h₀, h₁, hFp, hFt⟩

end SerrePositivity.KST.LocalizingInvariants
