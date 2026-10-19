module

public import SerrePositivity.InfinityCategories.F1B.KanNerveNatTransHomotopyFixedPoint
public import SerrePositivity.InfinityCategories.F1B.KanConePostcomposeNatTrans

/-!
概要：自然変換による錐の後合成を頂点を固定したホモトピーで表す。
方針：指数比較の成分公式と区間の Yoneda 表示を使う。
規約：図式上では元の指定変換を保持する。
使われ方：B5 の指定余単位の局所錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F G : I ⥤ C}

/-- 概要：錐の脚の後合成を元の nerve の join の錐のホモトピーとして表す。
方針：指定自然変換の成分と join の包含を比較する。
規約：同じ宇宙の小さい圏の元の図式を保つ。
使われ方：B5 の指定局所錐の古典比較。 -/
def kanNerveConePostcomposeHomotopy (c : Cone F) (η : F ⟶ G) :
    SSet.Homotopy (kanNerveCone c).val (kanNerveCone ((Cone.postcompose η).obj c)).val where
  h := ((HomotopyLimits.initialJoinNerveIso I).hom ▷ (Δ[1] : SSet.{u})) ≫
    (kanNerveNatTransHomotopy (kanConePostcomposeNatTrans c η)).h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, SSet.Homotopy.h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, SSet.Homotopy.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：錐のホモトピーは元の図式上で指定自然変換に一致する。
方針：指定自然変換の成分と join の包含を比較する。
規約：同じ宇宙の小さい圏の元の図式を保つ。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma kanNerveConePostcomposeHomotopy_diagram (c : Cone F) (η : F ⟶ G) :
    (joinInr (Δ[0] : SSet.{u}) (nerve I) ▷ (Δ[1] : SSet.{u})) ≫
      (kanNerveConePostcomposeHomotopy c η).h =
      (kanNerveNatTransHomotopy η).h := by
  change (joinInr (Δ[0] : SSet.{u}) (nerve I) ▷ (Δ[1] : SSet.{u})) ≫
    ((HomotopyLimits.initialJoinNerveIso I).hom ▷ (Δ[1] : SSet.{u})) ≫
      (kanNerveNatTransHomotopy (kanConePostcomposeNatTrans c η)).h = _
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((joinInr (Δ[0] : SSet.{u}) (nerve I) ≫
    HomotopyLimits.initialJoinNerveMap I) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [HomotopyLimits.joinInr_initialJoinNerveMap, kanNerveNatTransHomotopy_whiskerLeft,
    kanConePostcomposeNatTrans_restrict]

/-- 概要：錐の脚を後合成するホモトピーは指定頂点で時間に定値。
方針：join の左包含を新しい始対象へ移し、恒等成分での定値性を使う。
規約：元の錐の頂点を全時間で固定する。
使われ方：B5 の右 Kan の比較錐の具体的輸送。 -/
lemma kanNerveConePostcomposeHomotopy_fixedVertex (c : Cone F) (η : F ⟶ G) :
    (joinInl (Δ[0] : SSet.{u}) (nerve I) ▷ (Δ[1] : SSet.{u})) ≫
        (kanNerveConePostcomposeHomotopy c η).h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        joinInl (Δ[0] : SSet.{u}) (nerve I) ≫ (kanNerveCone c).val := by
  change (joinInl (Δ[0] : SSet.{u}) (nerve I) ▷ (Δ[1] : SSet.{u})) ≫
    ((HomotopyLimits.initialJoinNerveIso I).hom ▷ (Δ[1] : SSet.{u})) ≫
      (kanNerveNatTransHomotopy (kanConePostcomposeNatTrans c η)).h = _
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((joinInl (Δ[0] : SSet.{u}) (nerve I) ≫
    HomotopyLimits.initialJoinNerveMap I) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [HomotopyLimits.joinInl_initialJoinNerveMap]
  rw [kanNerveNatTransHomotopy_fixedPoint (kanConePostcomposeNatTrans c η)
    (WithInitial.star : WithInitial I) c.pt rfl]
  change _ = fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
    joinInl (Δ[0] : SSet.{u}) (nerve I) ≫
      HomotopyLimits.initialJoinNerveMap I ≫ nerveMap (kanConeWithInitialFunctor c)
  rw [← Category.assoc (joinInl _ _), HomotopyLimits.joinInl_initialJoinNerveMap]
  rfl

end SerrePositivity.InfinityCategories.F1B
