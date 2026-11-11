module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StableHomotopyShiftComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberTriangle
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # D3 で写した cofiber 三角形の第三射

概要：安定構造の一回シフトから来る第三射を、実際の suspension 比較を使う式へ戻す。
方針：CommShift の一回比較を展開し、シフトと suspension の同型の逆合成を消す。
規約：任意の実際の cofiber 列。使われ方：D7 の cone 接続射との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- mapTriangle の第三射は suspension 比較を使って計算できる。 -/
lemma derivedCofiberTriangle_mor₃ (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S))
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.mapTriangle.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht)).mor₃ =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftIso S).hom.app t.hoShortComplex.X₁ := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)).inv.app _) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.commShiftIso (1 : ℤ)).hom.app _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceCommShift_one]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)).inv.app _) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)).hom.app _) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftIso S).hom.app _) = _
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
