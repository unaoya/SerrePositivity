module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativeRestriction

/-!
概要：底上の射に沿い、両射影を底変換した元の cocartesian Hom を制限する。
方針：厳密な局所 Hom 同型で前合成を移し、全パラメーターで元の作用を展開する。
規約：可変の底には quasicategory 性を要求しない。
使われ方：各底変換の元の Hom による降下と分類写像の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
  {a b : Over B} (f : a ⟶ b)

/-- 底上の射による、両射影を底変換した元の cocartesian Hom の制限。 -/
def cocartesianPullbackNativePre :
    cocartesianRelativeFunctorSpace (pullback.fst b.hom p) (pullback.fst b.hom q) ⟶
      cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q) :=
  (cocartesianPullbackHomIso p q b).hom ≫ cocartesianPullbackHomPre p q f ≫
    (cocartesianPullbackHomIso p q a).inv

/-- 元の Hom の制限は、局所 Hom 同型と厳密に可換。 -/
lemma cocartesianPullbackNativePre_iso :
    cocartesianPullbackNativePre p q f ≫ (cocartesianPullbackHomIso p q a).hom =
      (cocartesianPullbackHomIso p q b).hom ≫ cocartesianPullbackHomPre p q f := by
  simp only [cocartesianPullbackNativePre, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 制限した族を元の標的へ射影すると、元の全空間の誘導射による実際の前合成になる。 -/
lemma cocartesianPullbackNativePre_uncurry_snd {T : SSet.{u}}
    (k : T ⟶ cocartesianRelativeFunctorSpace (pullback.fst b.hom p) (pullback.fst b.hom q)) :
    relativeFunctorUncurry ((k ≫ cocartesianPullbackNativePre p q f) ≫
      cocartesianRelativeFunctorInclusion (pullback.fst a.hom p) (pullback.fst a.hom q)) ≫
      pullback.snd a.hom q =
    (((overPullbackUnderlying p).map f) ▷ T) ≫
      relativeFunctorUncurry (k ≫ cocartesianRelativeFunctorInclusion
        (pullback.fst b.hom p) (pullback.fst b.hom q)) ≫ pullback.snd b.hom q := by
  unfold cocartesianPullbackNativePre
  rw [← Category.assoc k, ← Category.assoc (k ≫ (cocartesianPullbackHomIso p q b).hom),
    cocartesianPullbackHomIso_inv_uncurry_snd]
  unfold cocartesianPullbackHomPre
  refine (markedCocartesianFunctorUncurry_overPre q
    ((Over.pullback p ⋙ Over.map p).map f)
    {e | IsCocartesianEdge (pullback.fst a.hom p) e}
    {e | IsCocartesianEdge (pullback.fst b.hom p) e}
    (fun e he ↦ isCocartesianEdge_overPullback_map p f e he)
    (k ≫ (cocartesianPullbackHomIso p q b).hom)).trans ?_
  change (((overPullbackUnderlying p).map f) ▷ T) ≫
    markedCocartesianFunctorUncurry (k ≫ (cocartesianPullbackHomIso p q b).hom) = _
  rw [cocartesianPullbackHomIso_hom_uncurry]

end SerrePositivity.InfinityCategories
