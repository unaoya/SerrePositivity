module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCanonicalShapeLaws
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Edges
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
概要：標準右Kan錐による前合成を、図式側の制限と頂点の指定の両方で照合する。
方針：同じ標準形状の両制限の法則と、既存の閉構造の前合成則を使う。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存標準錐の計算法則。
使われ方：S8 の元の大域比較のhom_facと頂点成分を同じ形状で評価する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 元の標準形状の図式側への制限は、元の添字写像による前合成と可換。 -/
lemma rightKanCanonicalShape_precomposition {K C D : SSet.{u}}
    (δ : K ⟶ C) (c : C _⦋0⦌) :
    (pre (rightKanCanonicalShape δ c)).app D ≫
      (pre (joinInr (Δ[0] : SSet.{u}) (rightKanShape δ c))).app D =
    (pre δ).app D ≫ (pre (rightKanProjection δ c)).app D := by
  rw [← NatTrans.comp_app, ← pre_map, rightKanCanonicalShape_inr,
    pre_map, NatTrans.comp_app]

/-- 同じ標準形状の頂点は、元の指定頂点を返す。 -/
lemma rightKanCanonicalShape_apex {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (rightKanCanonicalShape δ c).app (Opposite.op ⦋0⦌)
      ((joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c)).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm 0)) = c := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm 0)) (rightKanCanonicalShape_inl δ c)
  change _ = (SSet.yonedaEquiv.symm c).app _ (stdSimplex.obj₀Equiv.symm 0) at h
  rw [SSet.yonedaEquiv_symm_zero] at h
  change _ = Basic.PinchedHom.constant c 0 at h
  rw [constant_zero] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
