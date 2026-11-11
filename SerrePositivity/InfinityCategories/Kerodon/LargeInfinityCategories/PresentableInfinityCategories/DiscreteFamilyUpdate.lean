module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiscreteDiagramVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：持ち上げた離散図式の指定した一成分だけを変える全関手族。
方針：離散成分を全次数で判定して内部 Hom へ curry する。
規約：他の成分は元の全図式のまま保持する。
使われ方：有限余積比較の Yoneda 生成による各変数の検出。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {I : Type u} {X : SSet.{u + 1}}
local instance : DecidableEq I := Classical.decEq I

/-- 概要：指定成分を変数に置き換える全評価図式。
方針：元の小さい離散成分を判定する。
規約：元の他成分を保持する。
使われ方：座標更新全関手の uncurry。 -/
def discreteFamilyUpdateEvaluation
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X) (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⊗ X ⟶ X where
  app n := ↾fun z ↦ if _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent z.1.down = i then z.2 else p.app n z.1
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨s⟩, x⟩
    change (if _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent ((nerve (Discrete I)).map α s) = i then X.map α x
      else p.app m (ULift.up ((nerve (Discrete I)).map α s))) =
      X.map α (if _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent s = i then x else p.app n (ULift.up s))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent_map]
    split_ifs with h
    · rfl
    · exact congrArg (fun f : ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (Discrete I))).obj n ⟶ X.obj m ↦ f (ULift.up s)) (p.naturality α)

/-- 概要：指定した一つの離散成分を変える全関手。
方針：同じ全評価図式を curry する。
規約：全ての変数値を一つの関手で扱う。
使われ方：生成表示の各座標への適用。 -/
def discreteFamilyUpdate
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X) (i : I) :
    X ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)))).obj X :=
  curry (discreteFamilyUpdateEvaluation p i)

/-- 概要：更新する座標では恒等、他の座標では元の頂点への定値関手を得る。
方針：curry の評価公式と離散成分の計算を使う。
規約：元の全関手の厳密な等式である。
使われ方：座標更新の sifted 余極限保存。 -/
lemma discreteFamilyUpdate_evaluate
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X) (i j : I) :
    discreteFamilyUpdate p i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))) =
      if j = i then 𝟙 X else SSet.const (p.app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))) := by
  rw [discreteFamilyUpdate, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change (if _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)) n) = i then x else
      p.app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))) n)) = _
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)) n) = j := rfl
  rw [hj]
  by_cases h : j = i
  · simp only [ite_eq_left h]
    rfl
  · simp only [ite_eq_right h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map p _ n

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
