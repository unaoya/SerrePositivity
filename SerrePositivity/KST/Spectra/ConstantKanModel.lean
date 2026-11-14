module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.DiscreteKanHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.DiscreteComponentLabels
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits

/-!
概要：離散成分を表す定値単体集合を、同じ離散圏の Kan nerve と照合する。
方針：既存の成分ラベル射を逆射に用い、離散圏の全射が恒等であることを使う。
規約：成分射を再定義せず、既存の実射を同型へ束ねる。
使われ方：Sp-7 の Kan ホモトピー消滅判定の離散標的。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 概要：既存の離散成分の実写像は、同じ定値対象との同型を与える。
方針：既存の成分ラベル射を逆射に用い、離散圏の全射が恒等であることを使う。
規約：成分射を再定義せず、既存の実射を同型へ束ねる。
使われ方：Sp-7 の Kan ホモトピー消滅判定の離散標的。 -/
def constantKanNerveIso (T : Type u) :
    ((Functor.const SimplexCategoryᵒᵖ).obj T : SSet.{u}) ≅ nerve (Discrete T) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.constantToDiscreteNerve T
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentLabelMap _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.discreteNerveComponent T)
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro F
    change (Functor.const (Fin (n.unop.len + 1))).obj (Discrete.mk (F.obj 0).as) = F
    fapply CategoryTheory.Functor.ext
    · intro i
      apply Discrete.ext
      exact Discrete.eq_of_hom (F.map (homOfLE (Fin.zero_le i)))
    · change ∀ (i j : Fin (n.unop.len + 1)) (a : i ⟶ j), _
      intros
      apply Subsingleton.elim

/-- 概要：同じ定値対象は追加のモデル構造なしに Kan 複体。
方針：既存の成分ラベル射を逆射に用い、離散圏の全射が恒等であることを使う。
規約：成分射を再定義せず、既存の実射を同型へ束ねる。
使われ方：Sp-7 の Kan ホモトピー消滅判定の離散標的。 -/
instance constantKanComplex (T : Type u) :
    KanComplex ((Functor.const SimplexCategoryᵒᵖ).obj T : SSet.{u}) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.discreteNerve_kanComplex T
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (constantKanNerveIso T).symm

end SerrePositivity.KST.Spectra
