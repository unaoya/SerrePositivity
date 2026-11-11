module
public import SerrePositivity.KST.SConstruction.StableModels
public import SerrePositivity.KST.SConstruction.DGApplication
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories

/-! # 実 S_n の安定値と元の完全射
概要：元の全 gapped S_n と cofiber 型の後合成を、安定 ∞ 圏と完全関手に束ねる。
方針：既存の安定性と cofiber 保存をそのまま使い、実単体集合と実作用を保持する。
規約：豊穣作用は後続で構成する。使われ方：全パラメータ S• の実値と通常射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.InfinityCategories
open LocalizingInvariants

/-- 全 gapped 図式からなる元の S_n を、同じ実安定 ∞ 圏として保持する。 -/
def sExactCategory (n : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} :=
  ⟨sConstruction n C.obj, inferInstance, inferInstance⟩

/-- 元の cofiber 型の S_n 後合成は、全零対象と cofiber 列を保つ。 -/
lemma sExactMap_isExactFunctor (n : ℕ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (sPostcompCofiber n F.hom (preservesCofiberData_of_isExactFunctor F.hom)) := by
  have h := preservesCofiberData_sPostcompCofiber n F.hom
    (preservesCofiberData_of_isExactFunctor F.hom)
  exact ⟨h.1, fun t ht => h.2 t ht⟩

/-- 元の同じ S_n 後合成を、安定 ∞ 圏間の完全射に束ねる。 -/
def sExactMap (n : ℕ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (sExactCategory n C) (sExactCategory n D) :=
  ⟨sPostcompCofiber n F.hom (preservesCofiberData_of_isExactFunctor F.hom),
    sExactMap_isExactFunctor n F⟩

/-- 元の S_n の通常作用は恒等・合成を厳密に保つ。 -/
def sExactEndofunctor (n : ℕ) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} ⥤ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} where
  obj := sExactCategory n
  map := sExactMap n
  map_id C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (sPostcompCofiber_id n C.obj)
  map_comp F G := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (sPostcompCofiber_comp n F.hom G.hom
    (preservesCofiberData_of_isExactFunctor F.hom)
    (preservesCofiberData_of_isExactFunctor G.hom))

/-- 元の全ての面退化による添字制限を、同じ実 S_n 間の完全射として使う。 -/
def sExactRestriction {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (sExactCategory n C) (sExactCategory m C) :=
  ⟨sMap C.obj θ, by
    have h := preservesCofiberData_sMap C.obj θ
    exact ⟨h.1, fun t ht => h.2 t ht⟩⟩

end SerrePositivity.KST.SConstruction
