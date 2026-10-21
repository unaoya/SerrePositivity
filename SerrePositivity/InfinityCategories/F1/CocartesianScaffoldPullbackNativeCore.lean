module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldPullbackMarkedCore

/-!
概要：両射影を引き戻した元の native Hom の core から、同じ scaffold Hom への比較。
方針：元の全相対 Hom の厳密な同型を同じ前合成へ合成する。
規約：元の native Hom の全高次と底の制限を保持する。
使われ方：セル貼合せの元の native 延長空間を scaffold の相対比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) [CocartesianFibration p] (q : F ⟶ nerve C)
  [CocartesianFibration q]

local instance (z : Over (nerve C)) : InnerFibration (pullback.fst z.hom q) :=
  ⟨innerFibrations.pullback_fst z.hom q (InnerFibration.mem (q := q))⟩

local instance (z : Over (nerve C)) : Quasicategory (cocartesianPullbackHomSpace p q z) :=
  inferInstanceAs (Quasicategory (markedCocartesianFunctorSpace q
    (pullback.snd z.hom p ≫ p) {e | IsCocartesianEdge (pullback.fst z.hom p) e}))

local instance (z : Over (nerve C)) :
    Quasicategory (cocartesianScaffoldPullbackMarkedHom p q z) :=
  inferInstanceAs (Quasicategory (markedCocartesianFunctorSpace q _
    (cocartesianScaffoldPullbackMark p z)))

local instance (z : Over (nerve C)) : KanComplex
    (quasicategoryCoreFunctor.obj
      (cocartesianRelativeFunctorSpace (pullback.fst z.hom p) (pullback.fst z.hom q))) :=
  inferInstanceAs (KanComplex (quasicategoryCore
    (cocartesianRelativeFunctorSpace (pullback.fst z.hom p) (pullback.fst z.hom q)) : SSet.{u}))

local instance (z : Over (nerve C)) :
    KanComplex (quasicategoryCoreFunctor.obj (cocartesianPullbackHomSpace p q z)) :=
  inferInstanceAs (KanComplex (quasicategoryCore (cocartesianPullbackHomSpace p q z) : SSet.{u}))

/-- 元の native Hom の core に作用する同じ scaffold 比較。 -/
def cocartesianScaffoldPullbackNativeCorePre (a : Over (nerve C)) :=
  (quasicategoryCoreFunctor.mapIso (cocartesianPullbackHomIso p q a)).hom ≫
    cocartesianScaffoldPullbackMarkedCorePre p q a

/-- 元の native Hom の core の同じ比較は、任意の部分底で同値。 -/
lemma cocartesianScaffoldPullbackNativeCorePre_isQCatEquivalence (a : Over (nerve C)) :
    IsQCatEquivalence (cocartesianScaffoldPullbackNativeCorePre p q a) :=
  (qCatEquivalenceOfIso
    (quasicategoryCoreFunctor.mapIso (cocartesianPullbackHomIso p q a))).isQCatEquivalence.comp
      (cocartesianScaffoldPullbackMarkedCorePre_isQCatEquivalence p q a)

/-- 元の native Hom の同じ比較も、部分底の制限と厳密に可換。 -/
lemma cocartesianScaffoldPullbackNativeCorePre_naturality
    {a b : Over (nerve C)} (f : a ⟶ b) :
    cocartesianScaffoldPullbackNativeCorePre p q b ≫
      cocartesianScaffoldPullbackMarkedCoreRestriction p q f =
    quasicategoryCoreMap (cocartesianPullbackNativePre p q f) ≫
      cocartesianScaffoldPullbackNativeCorePre p q a := by
  unfold cocartesianScaffoldPullbackNativeCorePre
  change (quasicategoryCoreFunctor.map (cocartesianPullbackHomIso p q b).hom ≫ _) ≫ _ =
    quasicategoryCoreFunctor.map (cocartesianPullbackNativePre p q f) ≫
      (quasicategoryCoreFunctor.map (cocartesianPullbackHomIso p q a).hom ≫ _)
  rw [Category.assoc, cocartesianScaffoldPullbackMarkedCorePre_naturality]
  change quasicategoryCoreFunctor.map _ ≫
    (quasicategoryCoreFunctor.map _ ≫ _) =
    quasicategoryCoreFunctor.map _ ≫ (quasicategoryCoreFunctor.map _ ≫ _)
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← cocartesianPullbackNativePre_iso, CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories
