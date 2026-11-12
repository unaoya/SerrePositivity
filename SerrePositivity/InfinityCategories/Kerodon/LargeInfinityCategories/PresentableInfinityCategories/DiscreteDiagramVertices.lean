module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：離散 nerve の全単体を成分頂点の退化単体として表示する。
方針：離散圏の全ての射が端点の等式を与えることを使う。
規約：小さい元の添字と宇宙持ち上げを区別する。
使われ方：有限余積の全関手族の座標を一つずつ変える。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：離散 nerve の単体が属する元の成分。
方針：零番頂点の離散対象を読む。
規約：元の小さい添字を返す。
使われ方：図式族の座標の判定。 -/
def discreteNerveComponent {I : Type u} {n : SimplexCategoryᵒᵖ}
    (s : (nerve (Discrete I)).obj n) : I := (s.obj 0).as

/-- 概要：離散成分は任意の単体作用で変わらない。
方針：零番頂点から像の頂点への離散射を読む。
規約：全ての単体作用を扱う。
使われ方：座標を指定する全関手の自然性。 -/
lemma discreteNerveComponent_map {I : Type u} {n m : SimplexCategoryᵒᵖ}
    (α : n ⟶ m) (s : (nerve (Discrete I)).obj n) :
    discreteNerveComponent ((nerve (Discrete I)).map α s) = discreteNerveComponent s :=
  (Discrete.eq_of_hom (s.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0))))).symm

/-- 概要：離散 nerve の全単体は同じ成分頂点の定値退化単体。
方針：元の ordinal 上の関手の全対象を離散射で比較する。
規約：全単体の厳密な等式である。
使われ方：離散図式の頂点による外延性。 -/
lemma discreteNerve_simplex_eq_constant {I : Type u} {n : ℕ}
    (s : (nerve (Discrete I)) _⦋n⦌) :
    s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (discreteNerveComponent s))) n := by
  apply CategoryTheory.Functor.ext
    (fun i ↦ by
      change s.obj i = Discrete.mk (discreteNerveComponent s)
      apply Discrete.ext
      exact (Discrete.eq_of_hom (s.map (homOfLE (Fin.zero_le i)))).symm)

/-- 概要：持ち上げた離散図式は元の成分頂点の値で決まる。
方針：全単体を同じ頂点の定値退化へ戻す。
規約：全図式の射の等式を結論する。
使われ方：座標の更新後に元の図式を回収する。 -/
lemma liftedDiscreteDiagram_hom_ext {I : Type u} {X : SSet.{u + 1}}
    {p q : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X}
    (h : ∀ i, p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i))) =
      q.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i)))) : p = q := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  have hs : (ULift.up s : ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (Discrete I))) _⦋n⦌) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (discreteNerveComponent s)))) n := by
    change ULift.up s = ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (discreteNerveComponent s))) n)
    exact congrArg ULift.up (discreteNerve_simplex_eq_constant s)
  rw [hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, h]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
