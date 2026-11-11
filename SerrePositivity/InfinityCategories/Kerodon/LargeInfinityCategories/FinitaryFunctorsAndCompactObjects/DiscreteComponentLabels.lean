module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentLabels
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
概要：連結成分のラベルを、元の離散 Kan nerve への射として検査する。
方針：元の定値対象を離散圏の nerve へ送り、その連結成分からラベルを回収する。
規約：元の全空間の Kan 性は要求しない。離散標的の Kan 性を証明する。
使われ方：弱ホモトピー同値の π₀ 全射性と、元の余極限の点の回収。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の定値対象を、同じ元の型の離散圏の nerve へ送る実写像。 -/
def constantToDiscreteNerve (T : Type u) :
    (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj T ⟶ nerve (Discrete T) where
  app n := ↾fun t ↦ (CategoryTheory.Functor.const (Fin (n.unop.len + 1))).obj (Discrete.mk t)
  naturality _ _ _ := rfl

/-- 元の離散圏の nerve は、追加のモデル構造なしに Kan 複体。 -/
lemma discreteNerve_kanComplex (T : Type u) : KanComplex (nerve (Discrete T)) := by
  let e : hoFunctor.obj (nerve (Discrete T)) ≌ Discrete T :=
    Cat.equivOfIso (nerveFunctorCompHoFunctorIso.app (Cat.of (Discrete T)))
  have : IsGroupoid (hoFunctor.obj (nerve (Discrete T))) := isGroupoid_of_reflects_iso e.functor
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid _

/-- 離散 nerve の同じ連結成分から、元の型のラベルを回収する。 -/
def discreteNerveComponent (T : Type u) : SSet.π₀ (nerve (Discrete T)) → T :=
  SSet.π₀.lift (fun x ↦ (x.obj 0).as) (fun _ _ e ↦ by
    have h := Discrete.eq_of_hom (e.edge.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))
    have hs := congrArg (fun v ↦ (v.obj 0).as) e.src_eq
    have ht := congrArg (fun v ↦ (v.obj 0).as) e.tgt_eq
    exact hs.symm.trans (h.trans ht))

/-- 連結成分の元のラベルを、同じ離散 Kan 標的で検査する実写像。 -/
def discreteComponentLabel (X : SSet.{u}) {T : Type u} (a : SSet.π₀ X → T) :
    X ⟶ nerve (Discrete T) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentLabelMap X a ≫ constantToDiscreteNerve T

/-- 同じ元の頂点に戻すと、元の連結成分のラベルを厳密に回収する。 -/
lemma discreteComponentLabel_zero (X : SSet.{u}) {T : Type u} (a : SSet.π₀ X → T)
    (x : X _⦋0⦌) : discreteNerveComponent T
      (SSet.π₀.mk ((discreteComponentLabel X a).app (Opposite.op ⦋0⦌) x)) =
        a (SSet.π₀.mk x) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentLabelMap X a).app (Opposite.op ⦋0⦌) x = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentLabelMap_zero X a x

/-- 元の離散 Kan 標的への全ラベルも、元の射への前合成に厳密に整合する。 -/
lemma discreteComponentLabel_pre {X Y : SSet.{u}} (f : X ⟶ Y) {T : Type u}
    (a : SSet.π₀ Y → T) :
    f ≫ discreteComponentLabel Y a = discreteComponentLabel X (a ∘ SSet.mapπ₀ f) := by
  rw [discreteComponentLabel, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentLabelMap_pre]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
