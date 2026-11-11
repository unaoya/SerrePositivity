module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyPath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathMap

/-!
概要：写像空間の族のホモトピーの表示とパラメータ前合成の整合性。
方針：raw な円柱の射の前合成を正方形と可逆 path の図式へ移す。
規約：端点の正規化に依存せず、指定ホモトピーそのものの射で判定する。
使われ方：B1 の導来 fiber の普遍族から選んだ輸送の前合成。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：ホモトピーの raw な前合成は関手正方形の前合成と一致する。
方針：区間族の展開と座標交換の自然性を使う。
規約：端点の表示は独立に正規化されていてよい。
使われ方：普遍ホモトピーを制限した正方形の認識。 -/
lemma intervalFamilySquare_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    {f₀ g₀ : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y} {f₁ g₁ : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y}
    (i : A ⟶ B) (H₀ : SSet.Homotopy f₀ g₀) (H₁ : SSet.Homotopy f₁ g₁)
    (h : H₀.h = (i ▷ (Δ[1] : SSet.{u})) ≫ H₁.h) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilySquare H₀ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilySquare H₁ ≫ (pre i).app X := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  change uncurry (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilySquareReorder A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry H₀.h)) =
    (i ▷ ((Δ[1] : SSet.{u}) ⊗ Δ[1])) ≫
      uncurry (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilySquareReorder B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry H₁.h))
  rw [uncurry_curry, uncurry_curry, h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilySquareReorder A ≫ (Δ[1] : SSet.{u}) ◁ (i ▷ (Δ[1] : SSet.{u})) =
      (i ▷ ((Δ[1] : SSet.{u}) ⊗ Δ[1])) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilySquareReorder B := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hs, Category.assoc]

/-- 概要：指定ホモトピーの可逆 path はパラメータ前合成と厳密に可換。
方針：包含で検査し、関手正方形の前合成公式を使う。
規約：同じ両端の別の path を選ばない。
使われ方：復元側の普遍境界 path を元のパラメータ上で照合する。 -/
lemma intervalFamilyPath_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    {f₀ g₀ : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y} {f₁ g₁ : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y}
    (i : A ⟶ B) (H₀ : SSet.Homotopy f₀ g₀) (H₁ : SSet.Homotopy f₁ g₁)
    (h : H₀.h = (i ▷ (Δ[1] : SSet.{u})) ≫ H₁.h) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyPath H₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyPath H₀ := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom A).obj X)) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom A).obj X))).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyPath_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyPath_ι]
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_curry, uncurry_curry, intervalFamilySquare_precomp i H₀ H₁ h]
  exact Category.assoc _ _ _

/-- 概要：定値可逆 path は単体集合の射への後合成と厳密に可換。
方針：包含後に curry の自然性で検査する。
規約：標的の quasicategory 性は不要。
使われ方：前合成後も三角形の固定二辺の path が定値であることの確認。 -/
lemma equivalencePathRefl_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap f = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathRefl_ι,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathRefl_ι]
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_curry, uncurry_natural_left, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
