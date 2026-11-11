module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cone
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：元の nerve の任意の join の錐から通常の錐を復元する。
方針：nerve の充満忠実性で関手を読み固定図式の等式を保つ。
規約：比較射の構成と普遍性の証明を区別する。
使われ方：B5 の pointwise Kan の古典比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：native な錐の全図式を通常の拡張関手として復元する。
方針：join の逆同型と nerve の充満忠実性を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def nerveConeReadFunctor (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap F)) : WithInitial I ⥤ C :=
  (nerveFunctor.preimage (X := Cat.of (WithInitial I)) (Y := Cat.of C)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).inv ≫ c.val)).toFunctor

/-- 概要：復元した関手の nerve は元の錐を再表示した射に等しい。
方針：nerve の逆像の仕様を読む。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma nerveConeReadFunctor_nerveMap (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap F)) :
    nerveMap (nerveConeReadFunctor c) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).inv ≫ c.val :=
  nerveFunctor.map_preimage (X := Cat.of (WithInitial I)) (Y := Cat.of C)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).inv ≫ c.val)

/-- 概要：復元した関手を元の添字へ制限すると元の図式になる。
方針：nerve の忠実性と join の右包含の公式を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma nerveConeReadFunctor_restrict (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap F)) :
    WithInitial.incl ⋙ nerveConeReadFunctor c = F := by
  have hh : (WithInitial.incl ⋙ nerveConeReadFunctor c).toCatHom = F.toCatHom := by
    apply nerveFunctor.map_injective
    change nerveMap (WithInitial.incl : I ⥤ WithInitial I) ≫
      nerveMap (nerveConeReadFunctor c) = nerveMap F
    rw [nerveConeReadFunctor_nerveMap, ← Category.assoc]
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_initialJoinNerveMap I
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve I) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).hom = _ at he
    rw [← he]
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_assoc]
    exact c.property
  exact congrArg Cat.Hom.toFunctor hh

/-- 概要：固定図式上の拡張関手を通常の錐へ戻す。
方針：始点の像とその構造射を図式の等式で輸送する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def coneFromWithInitialFunctor (G : WithInitial I ⥤ C) (h : WithInitial.incl ⋙ G = F) :
    Cone F where
  pt := G.obj WithInitial.star
  π := (WithInitial.mkCommaObject G).hom ≫ eqToHom h

/-- 概要：native な join の錐から通常の錐を復元する。
方針：関手を復元して元の図式上の錐として読む。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def coneOfNerveCone (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap F)) : Cone F :=
  coneFromWithInitialFunctor (nerveConeReadFunctor c) (nerveConeReadFunctor_restrict c)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
