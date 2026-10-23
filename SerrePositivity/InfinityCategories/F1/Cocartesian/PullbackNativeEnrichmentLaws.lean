module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeEvaluationLaws
public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeUnitHom

/-!
概要：元の全 cocartesian Hom の底変換は、豊穣単位と豊穣合成を厳密に保つ。
方針：二つの pullback 射影で検出し、元の全相対 Hom の評価公式を使う。
規約：元の全高次の作用を保持し、対象ごとの関手の選択へ置き換えない。
使われ方：cocartesian fibrations の ∞ 圏の間の底変換関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全相対 Hom の同じ底変換は豊穣単位を保つ。 -/
lemma cocartesianPullbackNativeRestriction_identity {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (a : Over B) :
    cocartesianRelativeFunctorIdentity (Over.mk p) ≫ cocartesianPullbackNativeRestriction p p a =
      cocartesianRelativeFunctorIdentity (Over.mk (pullback.fst a.hom p)) := by
  apply (cancel_mono (fullSubcomplexOnVertices _
    (cocartesianRelativeFunctorPredicate (pullback.fst a.hom p) (pullback.fst a.hom p))).ι).mp
  apply relativeFunctorUncurry_injective (pullback.fst a.hom p) (pullback.fst a.hom p)
  apply pullback.hom_ext
  · rw [relativeFunctorUncurry_projection, relativeFunctorUncurry_projection]
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    exact cocartesianPullbackNativeRestriction_apply_snd p p a
      ((cocartesianRelativeFunctorIdentity (Over.mk p)).app n t) x

/-- 元の全相対 Hom の同じ底変換は、全高次の豊穣合成を保つ。 -/
lemma cocartesianPullbackNativeRestriction_composition {E F G B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    (r : G ⟶ B) [CocartesianFibration r] (a : Over B) :
    cocartesianRelativeFunctorComposition (Over.mk p) (Over.mk q) (Over.mk r) ≫
      cocartesianPullbackNativeRestriction p r a =
    (cocartesianPullbackNativeRestriction p q a ⊗ₘ cocartesianPullbackNativeRestriction q r a) ≫
      cocartesianRelativeFunctorComposition (Over.mk (pullback.fst a.hom p))
        (Over.mk (pullback.fst a.hom q)) (Over.mk (pullback.fst a.hom r)) := by
  apply (cancel_mono (fullSubcomplexOnVertices _
    (cocartesianRelativeFunctorPredicate (pullback.fst a.hom p) (pullback.fst a.hom r))).ι).mp
  apply relativeFunctorUncurry_injective (pullback.fst a.hom r) (pullback.fst a.hom p)
  apply pullback.hom_ext
  · rw [relativeFunctorUncurry_projection, relativeFunctorUncurry_projection]
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, h, g⟩
    have hL := cocartesianPullbackNativeRestriction_apply_snd p r a
      ((cocartesianRelativeFunctorComposition (Over.mk p) (Over.mk q) (Over.mk r)).app n (h, g)) x
    have hR := cocartesianPullbackNativeRestriction_apply_snd q r a g
      ((((cocartesianPullbackNativeRestriction p q a).app n h).val.val.app n (𝟙 n)) x)
    have hH := cocartesianPullbackNativeRestriction_apply_snd p q a h x
    exact hL.trans (hR.trans (congrArg (fun y ↦ g.val.val.app n (𝟙 n) y) hH)).symm

end SerrePositivity.InfinityCategories
