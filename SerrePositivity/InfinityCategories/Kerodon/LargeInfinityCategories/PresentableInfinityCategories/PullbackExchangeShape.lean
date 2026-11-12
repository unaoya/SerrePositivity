module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CardinalExchangeShape
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
概要：引き戻しの cospan 形状について、濃度変更による filtered 余極限との交換を実証する。
方針：三対象の添字を有限 poset として模型化し、実証済みの poset 交換を移す。
規約：一般有限交換の未証明入力を要求しない。
使われ方：引き戻し候補の共変 Hom 全族の compact 性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

local instance (X Y : AsSmall.{u} WalkingCospan) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ULift.{u} (AsSmall.down.obj X ⟶ AsSmall.down.obj Y)))

/-- 概要：引き戻しの三つの添字を持つ小さい poset の台。
方針：元の walking cospan の対象を保持する。
規約：添字の宇宙は u。
使われ方：cospan 形状の poset 交換への移送。 -/
structure PullbackExchangeIndex : Type u where
  val : WalkingCospan

instance : PartialOrder PullbackExchangeIndex.{u} where
  le a b := a = b ∨ b.val = WalkingCospan.one
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | hb
    · exact hbc
    · rcases hbc with rfl | hc
      · exact Or.inr hb
      · exact Or.inr hc
  le_antisymm a b hab hba := by
    rcases hab with h | hb
    · exact h
    · rcases hba with h | ha
      · exact h.symm
      · cases a; cases b
        congr 1
        exact ha.trans hb.symm

instance : Finite PullbackExchangeIndex.{u} :=
  Finite.of_injective PullbackExchangeIndex.val (by
    intro a b h
    cases a; cases b
    cases h
    rfl)

/-- 概要：有限 poset から元の小さい cospan 圏への対象を保つ関手。
方針：恒等射と終点への二本の射を送る。
規約：元の cospan の両脚を保持する。
使われ方：添字の全 nerve 同型の順方向。 -/
def pullbackExchangeToCospan : PullbackExchangeIndex.{u} ⥤ AsSmall.{u} WalkingCospan where
  obj a := AsSmall.up.obj a.val
  map {a b} f := by
    by_cases h : a = b
    · exact eqToHom (congrArg (fun a : PullbackExchangeIndex.{u} ↦
        AsSmall.up.obj a.val) h)
    · have hb : b.val = WalkingCospan.one := (leOfHom f).resolve_left h
      cases a with | mk a =>
      cases b with | mk b =>
      change b = WalkingCospan.one at hb
      subst b
      cases a with
      | none => exact 𝟙 _
      | some i => exact AsSmall.up.map (WidePullbackShape.Hom.term i)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 概要：元の小さい cospan 圏から有限 poset への逆関手。
方針：元の三対象と二本の射を同じ順序関係へ送る。
規約：全射への作用を保持する。
使われ方：添字の全 nerve 同型の逆方向。 -/
def pullbackExchangeFromCospan : AsSmall.{u} WalkingCospan ⥤ PullbackExchangeIndex.{u} where
  obj a := ⟨AsSmall.down.obj a⟩
  map {a b} f := by
    have h (x y : WalkingCospan) (g : WidePullbackShape.Hom x y) :
        (⟨x⟩ : PullbackExchangeIndex.{u}) ≤ ⟨y⟩ := by
      cases g with
      | id _ => exact Or.inl rfl
      | term _ => exact Or.inr rfl
    exact homOfLE (h _ _ (AsSmall.down.map f))

/-- 概要：有限 poset の nerve と元の小さい cospan の nerve の全同型。
方針：両関手を各次数の全 composable arrows に適用する。
規約：全単体パラメーターで元の三対象を保つ。
使われ方：cospan の全錐交換の移送。 -/
def pullbackExchangeNerveIso : nerve PullbackExchangeIndex.{u} ≅
    nerve (AsSmall.{u} WalkingCospan) where
  hom := nerveMap pullbackExchangeToCospan
  inv := nerveMap pullbackExchangeFromCospan
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：元の小さい cospan の全極限錐は μ-filtered な全余極限で保たれる。
方針：有限 poset への全同型と実証済みの濃度変更交換を使う。
規約：形状交換を明示的に構成し、一般有限交換入力を要求しない。
使われ方：引き戻しの全共変 Hom の compact 性。 -/
lemma cardinalFilteredLimitExchangeShape_cospan
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CardinalFilteredLimitExchangeShape μ (nerve (AsSmall.{u} WalkingCospan)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.cardinalFilteredLimitExchangeShape_poset h PullbackExchangeIndex.{u}
    (hasCardinalLT_of_finite _ μ (Fact.out : μ.IsRegular).aleph0_le)).of_iso
  exact pullbackExchangeNerveIso

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
