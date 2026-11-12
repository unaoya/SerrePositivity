module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeExtension

/-!
概要：通常の余錐を終対象を付加した関手として表示する。
方針：標準余錐と拡張関手の像から元の余錐を復元する。
規約：元の図式と頂点、指定変換の全ての成分を保持する。
使われ方：B5 の左 Kan の局所余錐の指定単位に沿う輸送。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F G : I ⥤ C}


/-- 概要：余錐の脚の前合成を頂点で恒等な拡張関手間の自然変換にする。
方針：WithTerminal の対象と射の定義を計算する。
規約：同じ宇宙の小さい圏の元の余錐を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
def coconePrecomposeNatTrans (c : Cocone G) (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWithTerminalFunctor ((Cocone.precompose η).obj c) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWithTerminalFunctor c where
  app x := match x with
    | WithTerminal.of i => η.app i
    | WithTerminal.star => 𝟙 c.pt
  naturality i j f := by
    cases i with
    | of i =>
      cases j with
      | of j => exact η.naturality (WithTerminal.down f)
      | star =>
        change (η.app i ≫ c.ι.app i) ≫ 𝟙 c.pt = η.app i ≫ c.ι.app i
        exact Category.comp_id _
    | star =>
      cases j with
      | of j => exact (WithTerminal.false_of_from_star f).elim
      | star =>
        change 𝟙 c.pt ≫ 𝟙 c.pt = 𝟙 c.pt ≫ 𝟙 c.pt
        rfl

/-- 概要：余錐の前合成の拡張は元の指定自然変換に制限される。
方針：WithTerminal の対象と射の定義を計算する。
規約：同じ宇宙の小さい圏の元の余錐を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
lemma coconePrecomposeNatTrans_restrict (c : Cocone G) (η : F ⟶ G) :
    Functor.whiskerLeft WithTerminal.incl (coconePrecomposeNatTrans c η) = η := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
