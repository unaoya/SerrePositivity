module

public import SerrePositivity.InfinityCategories.F1B.KanNerveConeRead

/-!
概要：錐と WithInitial の拡張関手の復元を照合する。
方針：関手の拡張性を各対象と各種類の射に適用する。
規約：比較射の構成と普遍性の証明を区別する。
使われ方：B5 の pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：移した通常の錐を読み戻すと元の拡張関手になる。
方針：nerve の忠実性と join の逆性を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma kanNerveConeReadFunctor_of_cone (c : Cone F) :
    kanNerveConeReadFunctor (kanNerveCone c) = kanConeWithInitialFunctor c := by
  have h : (kanNerveConeReadFunctor (kanNerveCone c)).toCatHom =
      (kanConeWithInitialFunctor c).toCatHom := by
    apply nerveFunctor.map_injective
    change nerveMap (kanNerveConeReadFunctor (kanNerveCone c)) =
      nerveMap (kanConeWithInitialFunctor c)
    rw [kanNerveConeReadFunctor_nerveMap]
    change (HomotopyLimits.initialJoinNerveIso I).inv ≫
      ((HomotopyLimits.initialJoinNerveIso I).hom ≫ nerveMap (kanConeWithInitialFunctor c)) = _
    exact Iso.inv_hom_id_assoc _ _
  exact congrArg Cat.Hom.toFunctor h

/-- 概要：移した錐から元の通常の錐を回収する。
方針：復元した関手の等式と成分の式を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma kanConeOfNerveCone_of_cone (c : Cone F) : kanConeOfNerveCone (kanNerveCone c) = c := by
  dsimp only [kanConeOfNerveCone]
  simp only [kanNerveConeReadFunctor_of_cone]
  change kanConeFromWithInitialFunctor (kanConeWithInitialFunctor c) rfl = c
  dsimp only [kanConeFromWithInitialFunctor]
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
lemma kanConeWithInitialFunctor_of_functor (G : WithInitial I ⥤ C) (h : WithInitial.incl ⋙ G = F) :
    kanConeWithInitialFunctor (kanConeFromWithInitialFunctor G h) = G := by
  let hx : ∀ x, (kanConeWithInitialFunctor (kanConeFromWithInitialFunctor G h)).obj x =
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

end SerrePositivity.InfinityCategories.F1B
