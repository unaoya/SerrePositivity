module

public import SerrePositivity.InfinityCategories.F1.CocartesianAnodyneHomComparison
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldPullbackNativeLift

/-!
概要：inner anodyne 部分底の辺保存 scaffold Hom を、実際の分類先の区間 Hom と比較する。
方針：同じ native scaffold 比較の逆に、元の native Hom の分類先比較を合成する。
規約：scaffold の像だけへの分類に置き換えず、元の大域 Hom 作用との関手同型を保持する。
使われ方：実際の内ホーンを使った境界の帰納の target 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (n : ℕ)
  (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin (n + 1)))))
  (a : Over (nerve (ULift.{u} (Fin (n + 1)))))
  (ha : innerAnodyneExtensions a.hom)
  (he : Function.Surjective (a.hom.app (Opposite.op ⦋1⦌)))

local instance : InnerFibration (pullback.fst a.hom q.val.hom) :=
  ⟨innerFibrations.pullback_fst a.hom q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

local instance : Quasicategory (cocartesianScaffoldPullbackMarkedHom p.val.hom q.val.hom a) :=
  inferInstanceAs (Quasicategory (markedCocartesianFunctorSpace q.val.hom _
    (cocartesianScaffoldPullbackMark p.val.hom a)))

local instance : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    (quasicategoryCoreFunctor.obj (cocartesianRelativeFunctorSpace
      (pullback.fst a.hom p.val.hom) (pullback.fst a.hom q.val.hom)))) :=
  inferInstanceAs (KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (quasicategoryCore
    (cocartesianRelativeFunctorSpace (pullback.fst a.hom p.val.hom)
      (pullback.fst a.hom q.val.hom)) : SSet.{u})))

/-- 同じ native scaffold 比較の逆を共有した、実際の分類先 Hom への射。 -/
def cocartesianAnodyneScaffoldTargetComparison :=
  (cocartesianScaffoldPullbackNativeLiftPre_isQCatEquivalence p.val.hom q.val.hom a).choose.inv ≫
    cocartesianAnodyneNativeHomComparison n p q a ha he

/-- 同じ scaffold 比較の後で、この target 比較は元の native target 比較に戻る。 -/
def cocartesianAnodyneScaffoldTargetComparison_nativeIso :
    FunctorIso
      (cocartesianScaffoldPullbackNativeLiftPre p.val.hom q.val.hom a ≫
        cocartesianAnodyneScaffoldTargetComparison n p q a ha he)
      (cocartesianAnodyneNativeHomComparison n p q a ha he) :=
  F2.functorIsoOfEq
    ((cocartesianScaffoldPullbackNativeLiftPre_isQCatEquivalence p.val.hom q.val.hom a).choose.homInvIso.postcomp
      (cocartesianAnodyneNativeHomComparison n p q a ha he))
    (by simp only [cocartesianAnodyneScaffoldTargetComparison, Category.assoc]; rfl)
    (Category.id_comp _)

/-- 元の同じ大域作用を、同じ部分底上の scaffold と分類先の比較を通して回収する。 -/
def cocartesianAnodyneScaffoldTargetComparison_originalIso :
    FunctorIso
      ((cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom a ≫
        cocartesianScaffoldPullbackNativeLiftPre p.val.hom q.val.hom a) ≫
          cocartesianAnodyneScaffoldTargetComparison n p q a ha he)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map a.hom)
          (cocartesianStrictTransportCoherentDiagram p.val.hom)
          (cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  F2.functorIsoOfEq
    ((cocartesianAnodyneScaffoldTargetComparison_nativeIso n p q a ha he).precomp
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom a))
    (Category.assoc _ _ _).symm rfl ≪≫
      cocartesianAnodyneNativeHomComparison_originalIso n p q a ha he

/-- 同じ scaffold からの実際の target 比較自身が同値。 -/
lemma cocartesianAnodyneScaffoldTargetComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianAnodyneScaffoldTargetComparison n p q a ha he) :=
  (cocartesianScaffoldPullbackNativeLiftPre_isQCatEquivalence p.val.hom q.val.hom a).choose.symm.isQCatEquivalence.comp
    (cocartesianAnodyneNativeHomComparison_isQCatEquivalence n p q a ha he)

end SerrePositivity.InfinityCategories
