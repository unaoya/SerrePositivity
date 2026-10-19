module

public import SerrePositivity.InfinityCategories.F1B.KanNerveConeRecovery

/-!
概要：通常の錐と native な join の錐の間の頂点を保つ全単射。
方針：両方向の関手の復元と join の同型の逆性を使う。
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

/-- 概要：復元した通常の錐を再び移すと元の native な錐になる。
方針：関手の復元と join の同型の逆性を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma kanNerveCone_of_read (c : JoinCone (nerveMap F)) :
    kanNerveCone (kanConeOfNerveCone c) = c := by
  apply Subtype.ext
  change (HomotopyLimits.initialJoinNerveIso I).hom ≫
    nerveMap (kanConeWithInitialFunctor (kanConeFromWithInitialFunctor
      (kanNerveConeReadFunctor c) (kanNerveConeReadFunctor_restrict c))) = c.val
  rw [kanConeWithInitialFunctor_of_functor, kanNerveConeReadFunctor_nerveMap]
  exact Iso.hom_inv_id_assoc _ _

/-- 概要：通常の錐と元の nerve の任意の join の錐の間の全単射。
方針：証明済みの二つの逆性をまとめる。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def kanNerveConeEquiv : Cone F ≃ JoinCone (nerveMap F) where
  toFun := kanNerveCone
  invFun := kanConeOfNerveCone
  left_inv := kanConeOfNerveCone_of_cone
  right_inv := kanNerveCone_of_read

/-- 概要：読み戻した通常の錐は元の native な頂点を表す。
方針：前向きの頂点公式と錐の右逆性を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma kanConeOfNerveCone_vertex (c : JoinCone (nerveMap F)) :
    nerveVertex (kanConeOfNerveCone c).pt = c.vertex := by
  have h := kanNerveCone_vertex (kanConeOfNerveCone c)
  rw [kanNerveCone_of_read] at h
  exact h.symm

end SerrePositivity.InfinityCategories.F1B
