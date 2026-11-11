module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeExtensionFunctor

/-!
概要：通常の自然変換と指定錐の後合成を実際のホモトピーへ移す。
方針：nerve の指数比較の辺を uncurry して成分を計算する。
規約：元の図式と自然変換を保ち、可逆性を仮定しない。
使われ方：B5 の指定単位・余単位の局所錐の比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F G : I ⥤ C}

/-- 概要：錐の脚の後合成を頂点で恒等な拡張関手間の自然変換にする。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
def conePostcomposeNatTrans (c : Cone F) (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor ((Cone.postcompose η).obj c) where
  app x := match x with
    | WithInitial.of i => η.app i
    | WithInitial.star => 𝟙 c.pt
  naturality i j f := by
    cases i with
    | of i =>
      cases j with
      | of j => exact η.naturality (WithInitial.down f)
      | star => exact (WithInitial.false_of_to_star f).elim
    | star =>
      cases j with
      | of j =>
        change c.π.app j ≫ η.app j = 𝟙 c.pt ≫ (c.π.app j ≫ η.app j)
        exact (Category.id_comp _).symm
      | star =>
        change 𝟙 c.pt ≫ 𝟙 c.pt = 𝟙 c.pt ≫ 𝟙 c.pt
        rfl

/-- 概要：錐の後合成の拡張は元の図式の自然変換へ制限される。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma conePostcomposeNatTrans_restrict (c : Cone F) (η : F ⟶ G) :
    Functor.whiskerLeft WithInitial.incl (conePostcomposeNatTrans c η) = η := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
