module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.RelativeOverPre

/-!
概要：元の底上の同型を、同じ宇宙持ち上げの底上の同型へ移す。
方針：忘却した同型を持ち上げ、元の底上の可換式を同じ関手で移す。
規約：順方向と逆方向は既存の底上の射の持ち上げと一致する。
使われ方：標準セルの表示同型で元の分類先 Hom を移す。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 同じ底上の同型の宇宙持ち上げ。 -/
def uliftOverIso {B : SSet.{u}} {a b : Over B} (e : a ≅ b) :
    Over.mk ((SSet.uliftFunctor.{v, u}).map a.hom) ≅
      Over.mk ((SSet.uliftFunctor.{v, u}).map b.hom) :=
  Over.isoMk ((SSet.uliftFunctor.{v, u}).mapIso ((Over.forget B).mapIso e)) (by
    change (SSet.uliftFunctor.{v, u}).map e.hom.left ≫
      (SSet.uliftFunctor.{v, u}).map b.hom = (SSet.uliftFunctor.{v, u}).map a.hom
    rw [← Functor.map_comp, e.hom.w])

/-- 同じ同型の順方向は既存の底上の射の持ち上げ。 -/
lemma uliftOverIso_hom {B : SSet.{u}} {a b : Over B} (e : a ≅ b) :
    (uliftOverIso.{u, v} e).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism e.hom := by
  apply Over.OverMorphism.ext
  rfl

/-- 同じ同型の逆方向も既存の底上の射の持ち上げ。 -/
lemma uliftOverIso_inv {B : SSet.{u}} {a b : Over B} (e : a ≅ b) :
    (uliftOverIso.{u, v} e).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism e.inv := by
  apply Over.OverMorphism.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
