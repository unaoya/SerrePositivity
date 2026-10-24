module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ConeRecovery

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
lemma nerveCone_of_read (c : JoinCone (nerveMap F)) :
    SerrePositivity.InfinityCategories.F1B.nerveCone (SerrePositivity.InfinityCategories.F1B.coneOfNerveCone c) = c := by
  apply Subtype.ext
  change (HomotopyLimits.initialJoinNerveIso I).hom ≫
    nerveMap (SerrePositivity.InfinityCategories.F1B.coneWithInitialFunctor (SerrePositivity.InfinityCategories.F1B.coneFromWithInitialFunctor
      (SerrePositivity.InfinityCategories.F1B.nerveConeReadFunctor c) (SerrePositivity.InfinityCategories.F1B.nerveConeReadFunctor_restrict c))) = c.val
  rw [SerrePositivity.InfinityCategories.F1B.coneWithInitialFunctor_of_functor, SerrePositivity.InfinityCategories.F1B.nerveConeReadFunctor_nerveMap]
  exact Iso.hom_inv_id_assoc _ _

/-- 概要：通常の錐と元の nerve の任意の join の錐の間の全単射。
方針：証明済みの二つの逆性をまとめる。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def nerveConeEquiv : Cone F ≃ JoinCone (nerveMap F) where
  toFun := SerrePositivity.InfinityCategories.F1B.nerveCone
  invFun := SerrePositivity.InfinityCategories.F1B.coneOfNerveCone
  left_inv := SerrePositivity.InfinityCategories.F1B.coneOfNerveCone_of_cone
  right_inv := nerveCone_of_read

/-- 概要：読み戻した通常の錐は元の native な頂点を表す。
方針：前向きの頂点公式と錐の右逆性を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma coneOfNerveCone_vertex (c : JoinCone (nerveMap F)) :
    nerveVertex (SerrePositivity.InfinityCategories.F1B.coneOfNerveCone c).pt = c.vertex := by
  have h := SerrePositivity.InfinityCategories.F1B.nerveCone_vertex (SerrePositivity.InfinityCategories.F1B.coneOfNerveCone c)
  rw [nerveCone_of_read] at h
  exact h.symm

end SerrePositivity.InfinityCategories.F1B
