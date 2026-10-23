module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeFunctor
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackRestrictionNaturality

/-!
概要：元の native core の制限と合成則・自然性を宇宙持ち上げ後も保持する。
方針：元の反変制限関手と core・ULift の関手性を使う。
規約：同じ元の全相対 Hom と制限写像を保持する。
使われ方：標準表示と nerve 表示の source Segal 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]

/-- 元の底上の制限の core を同じ大きい宇宙へ移した射。 -/
def cocartesianPullbackNativeLiftPre {a b : Over B} (f : a ⟶ b) :=
  (SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreMap (cocartesianPullbackNativePre p q f))

/-- 同じ持ち上げた制限は、元の底上の合成則を厳密に保つ。 -/
lemma cocartesianPullbackNativeLiftPre_comp {a b c : Over B} (f : a ⟶ b) (g : b ⟶ c) :
    cocartesianPullbackNativeLiftPre p q g ≫ cocartesianPullbackNativeLiftPre p q f =
      cocartesianPullbackNativeLiftPre p q (f ≫ g) := by
  change (SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreFunctor.map _) ≫
    (SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreFunctor.map _) = _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← cocartesianPullbackNativePre_comp]
  rfl

/-- 底上の同型による同じ持ち上げた native core 制限は同型。 -/
lemma cocartesianPullbackNativeLiftPre_isIso {a b : Over B} (f : a ⟶ b) [IsIso f] :
    IsIso (cocartesianPullbackNativeLiftPre p q f) := by
  change IsIso (((cocartesianPullbackNativeCoreFunctor p q) ⋙
    SSet.uliftFunctor.{u + 1, u}).map f.op)
  infer_instance

/-- 大域の元の native core から同じ底変換への制限の宇宙持ち上げ。 -/
def cocartesianPullbackNativeLiftRestriction (a : Over B) :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (quasicategoryCoreMap (cocartesianPullbackNativeRestriction p q a))

/-- 同じ元の大域制限は、持ち上げ後も元の底上の射で厳密に自然。 -/
lemma cocartesianPullbackNativeLiftRestriction_naturality {a b : Over B} (f : a ⟶ b) :
    cocartesianPullbackNativeLiftRestriction p q b ≫ cocartesianPullbackNativeLiftPre p q f =
      cocartesianPullbackNativeLiftRestriction p q a := by
  change (SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreFunctor.map _) ≫
    (SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreFunctor.map _) = _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    cocartesianPullbackNativeRestriction_naturality]
  rfl

end SerrePositivity.InfinityCategories
