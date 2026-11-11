module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：weighted nerve の係数図式の自然変換に関する関手性。
方針：各底の射列を保ち、重み付き図式に係数の自然変換を後合成する。
規約：底の nerve を固定した通常の圏 Over(nerve C) に値を取る。
使われ方：Kerodon §5.3.3（Tag 025W）、strict transport 表現の比較を全空間の比較へ移す操作。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：係数図式の自然変換は同じ底上の weighted nerve の射を誘導する。
方針：底の射列 σ を保ち、τ に σ 上の係数の自然変換を後合成する。
規約：係数図式の充填性は要求しない。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の係数に関する関手性。 -/
def weightedNerveMap {C : Type u} [Category.{u} C] {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G where
  app _ := ↾fun s ↦ ⟨s.1, s.2 ≫ CategoryTheory.Functor.whiskerLeft s.1 η⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    exact Category.assoc _ _ _

/-- 概要：weighted nerve の係数による射は底の射影を保つ。
方針：各次数の底の射列が変わらないことを使う。
規約：底は同じ通常の圏 C。
使われ方：Kerodon §5.3.3（Tag 025W）、Over(nerve C) の射としての weighted nerve 比較。 -/
lemma weightedNerveMap_projection {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    weightedNerveMap η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F := rfl

/-- 概要：係数の恒等変換による weighted nerve の射は恒等射。
方針：重み付き図式の各成分で恒等の後合成を消去する。
規約：F は任意の単体集合値関手。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve 関手の単位則。 -/
lemma weightedNerveMap_id {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    weightedNerveMap (𝟙 F) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  exact Category.comp_id _

/-- 概要：係数の自然変換の合成は weighted nerve の射の合成になる。
方針：重み付き図式の各成分で後合成の結合律を使う。
規約：η の後に θ を合成する。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve 関手の合成則。 -/
lemma weightedNerveMap_comp {C : Type u} [Category.{u} C]
    {F G H : C ⥤ SSet.{u}} (η : F ⟶ G) (θ : G ⟶ H) :
    weightedNerveMap (η ≫ θ) = weightedNerveMap η ≫ weightedNerveMap θ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  exact (Category.assoc _ _ _).symm

/-- 概要：weighted nerve を底の nerve 上の単体集合へ値を取る関手に束縛する。
方針：射影を Over の対象とし、係数の自然変換を底を保つ射にする。
規約：これは通常の圏の関手であり、∞ 圏の分類の同値性をまだ主張しない。
使われ方：Kerodon §5.3.3（Tag 025W）、strict diagram の比較と fibration の復元の基礎。 -/
def weightedNerveFunctor (C : Type u) [Category.{u} C] :
    (C ⥤ SSet.{u}) ⥤ Over (nerve C) where
  obj F := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)
  map η := Over.homMk (weightedNerveMap η) (weightedNerveMap_projection η)
  map_id F := by
    apply Over.OverMorphism.ext
    exact weightedNerveMap_id F
  map_comp η θ := by
    apply Over.OverMorphism.ext
    exact weightedNerveMap_comp η θ

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
