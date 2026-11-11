module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeRead

/-!
概要：錐と WithInitial の拡張関手の復元を照合する。
方針：関手の拡張性を各対象と各種類の射に適用する。
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

/-- 概要：移した通常の錐を読み戻すと元の拡張関手になる。
方針：nerve の忠実性と join の逆性を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma nerveConeReadFunctor_of_cone (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeReadFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c := by
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeReadFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c)).toCatHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c).toCatHom := by
    apply nerveFunctor.map_injective
    change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeReadFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c)) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeReadFunctor_nerveMap]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso I).hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c)) = _
    exact Iso.inv_hom_id_assoc _ _
  exact congrArg Cat.Hom.toFunctor h

/-- 概要：移した錐から元の通常の錐を回収する。
方針：復元した関手の等式と成分の式を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma coneOfNerveCone_of_cone (c : Cone F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneOfNerveCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c) = c := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneOfNerveCone]
  simp only [nerveConeReadFunctor_of_cone]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFromWithInitialFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c) rfl = c
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFromWithInitialFunctor]
  cases c
  congr 1
  apply NatTrans.ext
  funext i
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 概要：復元した通常の錐を拡張すると元の拡張関手になる。
方針：始点・元の対象と三種類の射を比較する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma coneWithInitialFunctor_of_functor (G : WithInitial I ⥤ C) (h : WithInitial.incl ⋙ G = F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFromWithInitialFunctor G h) = G := by
  let hx : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFromWithInitialFunctor G h)).obj x =
      G.obj x := by
    intro x
    cases x with
    | of i => exact (CategoryTheory.Functor.congr_obj h i).symm
    | star => rfl
  refine CategoryTheory.Functor.ext hx (fun i j f ↦ ?_)
  cases i with
  | of i =>
    cases j with
    | of j => exact CategoryTheory.Functor.congr_hom h.symm (WithInitial.down f)
    | star => exact (WithInitial.false_of_to_star f).elim
  | star =>
    cases j with
    | of j =>
      have hf : f = WithInitial.homTo j := Subsingleton.elim _ _
      rw [hf]
      simp only [eqToHom_refl, Category.id_comp]
      change ((WithInitial.mkCommaObject G).hom ≫ eqToHom h).app j = _
      simp only [NatTrans.comp_app, eqToHom_app]
      rfl
    | star =>
      have hf : f = 𝟙 WithInitial.star := Subsingleton.elim _ _
      rw [hf, G.map_id]
      simp only [eqToHom_refl, Category.comp_id]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
