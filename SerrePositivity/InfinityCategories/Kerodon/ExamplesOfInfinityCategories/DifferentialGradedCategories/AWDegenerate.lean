module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DegenerateEvaluation

/-!
# AW の接頭・接尾の退化項の消滅

概要：AW の一項は後の射の接頭成分または前の射の接尾成分が退化すれば零である。
方針：順序 nerve の頂点の重複から成分を零にし、dg 合成の零元の保存を使う。
規約：接頭側が後の射、接尾側が前の射。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0）–2.5.9（Tag 00SC） の AW と shuffle の積の計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：AW の接頭側の頂点が重複する項は零である。
方針：後の射の接頭成分を零にし、その合成を零にする。
規約：前の射の成分には退化の条件を課さない。
使われ方：Kerodon 2.5.8（Tag 00S0） の shuffle の前半に誤った座標を含む項の消去。 -/
lemma awTerm_nerve_zero_left {P : Type u} [PartialOrder P] {n : ℕ}
    (ψ : nerve P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z) (s : (nerve P) _⦋n⦌)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (J : Finset (Fin (n + 1))) (j : J)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (hs : ¬ Set.InjOn s.obj ((J.filter (· ≤ j.val)) : Set (Fin (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (ψ.app _ s).val f J j k hk = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardComponent_nerve_zero_of_not_injOn ψ s _ _ _ _ hs]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose _ _

/-- 概要：AW の接尾側の頂点が重複する項は零である。
方針：前の射の接尾成分を零にし、その合成を零にする。
規約：後の射の成分には退化の条件を課さない。
使われ方：Kerodon 2.5.8（Tag 00S0） の shuffle の後半に誤った座標を含む項の消去。 -/
lemma awTerm_nerve_zero_right {P : Type u} [PartialOrder P] {n : ℕ}
    (φ : nerve P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) (s : (nerve P) _⦋n⦌)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (J : Finset (Fin (n + 1))) (j : J)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (hs : ¬ Set.InjOn s.obj ((J.filter (j.val ≤ ·)) : Set (Fin (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g (φ.app _ s).val J j k hk = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardComponent_nerve_zero_of_not_injOn φ s _ _ _ _ hs]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
