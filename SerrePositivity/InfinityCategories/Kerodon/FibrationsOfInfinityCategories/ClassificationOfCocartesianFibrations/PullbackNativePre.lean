module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeRestriction

/-!
概要：底上の射に沿い、両射影を底変換した元の cocartesian Hom を制限する。
方針：厳密な局所 Hom 同型で前合成を移し、全パラメーターで元の作用を展開する。
規約：可変の底には quasicategory 性を要求しない。
使われ方：各底変換の元の Hom による降下と分類写像の自然性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
  {a b : Over B} (f : a ⟶ b)

/-- 底上の射による、両射影を底変換した元の cocartesian Hom の制限。 -/
def cocartesianPullbackNativePre :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst b.hom p) (pullback.fst b.hom q) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q b).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomPre p q f ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q a).inv

/-- 元の Hom の制限は、局所 Hom 同型と厳密に可換。 -/
lemma cocartesianPullbackNativePre_iso :
    cocartesianPullbackNativePre p q f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q a).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q b).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomPre p q f := by
  simp only [cocartesianPullbackNativePre, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 制限した族を元の標的へ射影すると、元の全空間の誘導射による実際の前合成になる。 -/
lemma cocartesianPullbackNativePre_uncurry_snd {T : SSet.{u}}
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst b.hom p) (pullback.fst b.hom q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry ((k ≫ cocartesianPullbackNativePre p q f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorInclusion (pullback.fst a.hom p) (pullback.fst a.hom q)) ≫
      pullback.snd a.hom q =
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map f) ▷ T) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorInclusion
        (pullback.fst b.hom p) (pullback.fst b.hom q)) ≫ pullback.snd b.hom q := by
  unfold cocartesianPullbackNativePre
  rw [← Category.assoc k, ← Category.assoc (k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q b).hom),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso_inv_uncurry_snd]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomPre
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry_overPre q
    ((Over.pullback p ⋙ Over.map p).map f)
    {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p) e}
    {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst b.hom p) e}
    (fun e he ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_overPullback_map p f e he)
    (k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q b).hom)).trans ?_
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map f) ▷ T) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry (k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q b).hom) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso_hom_uncurry]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
