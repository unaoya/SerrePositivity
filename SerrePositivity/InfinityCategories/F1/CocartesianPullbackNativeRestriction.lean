module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackHomIsoEvaluation
public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorFamilyLaws

/-!
概要：元の cocartesian Hom を、両射影を底変換した同じ cocartesian Hom へ制限する。
方針：元の標的への制限を厳密な pullback 同型で持ち上げ、二射影で作用を計算する。
規約：全パラメーターで実際の全空間への制限を保つ。
使われ方：元の分類写像と各底変換での分類写像の作用の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q] (a : Over B)

/-- 元の全 cocartesian Hom の、両射影を底変換した元の Hom への制限。 -/
def cocartesianPullbackNativeRestriction : cocartesianRelativeFunctorSpace p q ⟶
    cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q) :=
  cocartesianPullbackHomRestriction p q a ≫ (cocartesianPullbackHomIso p q a).inv

/-- 同じ底変換の制限は、元の標的へ戻す同型と厳密に可換。 -/
lemma cocartesianPullbackNativeRestriction_iso :
    cocartesianPullbackNativeRestriction p q a ≫ (cocartesianPullbackHomIso p q a).hom =
      cocartesianPullbackHomRestriction p q a := by
  simp only [cocartesianPullbackNativeRestriction, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- 全パラメーターの族の元の標的への射影は、元の全空間上の族の実際の制限。 -/
lemma cocartesianPullbackNativeRestriction_uncurry_snd {T : SSet.{u}}
    (k : T ⟶ cocartesianRelativeFunctorSpace p q) :
    relativeFunctorUncurry ((k ≫ cocartesianPullbackNativeRestriction p q a) ≫
      cocartesianRelativeFunctorInclusion (pullback.fst a.hom p) (pullback.fst a.hom q)) ≫
      pullback.snd a.hom q =
    (pullback.snd a.hom p ▷ T) ≫
      relativeFunctorUncurry (k ≫ cocartesianRelativeFunctorInclusion p q) := by
  unfold cocartesianPullbackNativeRestriction
  rw [← Category.assoc k, cocartesianPullbackHomIso_inv_uncurry_snd]
  unfold cocartesianPullbackHomRestriction
  exact markedCocartesianFunctorUncurry_overPre _ _ _ _ _ _

/-- 同じ族の底への射影は、始域の底変換の射影で固定される。 -/
lemma cocartesianPullbackNativeRestriction_uncurry_fst {T : SSet.{u}}
    (k : T ⟶ cocartesianRelativeFunctorSpace p q) :
    relativeFunctorUncurry ((k ≫ cocartesianPullbackNativeRestriction p q a) ≫
      cocartesianRelativeFunctorInclusion (pullback.fst a.hom p) (pullback.fst a.hom q)) ≫
      pullback.fst a.hom q = fst (pullback a.hom p) T ≫ pullback.fst a.hom p :=
  relativeFunctorUncurry_projection _

end SerrePositivity.InfinityCategories
