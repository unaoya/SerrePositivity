module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Stable.CospanFamilies
public import SerrePositivity.InfinityCategories.Stable.SquareHorizontalHomotopies
public import SerrePositivity.InfinityCategories.Core.Quasicategory.SimplexTerminalArrowFamily

/-!
分割で生成：docstring を書き直すこと
概要：有限線型図式の終端を指定辺に沿って引き戻し、終端の四角形を厳密に固定する。
方針：同じ終端辺族を cospan 族へ貼り、最後の頂点上の列四角形を保って相対延長する。
規約：終端での同型だけではなく、列四角形そのものを保持する。
使われ方：c5 の有限図式の持ち上げで、次の辺との共有端点を保つ精密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

variable {X : SSet.{u}} {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ X)
  (s : (Δ[1] : SSet.{u}) ⟶ X)
  (hs : s.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))

include hs in
/-- 同じ指定辺の定値族と、元の図式の終端辺族は厳密な終点を共有する。 -/
lemma simplexTerminalCospan_comm :
    (SSet.const (functorVertex s) : (Δ[n] : SSet.{u}) ⟶ _) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    simplexTerminalArrowFamily D ≫ evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [SSet.const_comp, evaluateFunctorAt_functorVertex, simplexTerminalArrowFamily_target, hs]

/-- 元の全図式と指定終端辺からなる、全単体上の同じ cospan 族。 -/
def simplexTerminalCospanFamily :
    (Δ[n] : SSet.{u}) ⟶ (ihom (horn 2 2 : SSet.{u})).obj X :=
  stable_cospanFamilyOfArrows (SSet.const (functorVertex s))
    (simplexTerminalArrowFamily D) (simplexTerminalCospan_comm D s hs)

/-- cospan の右辺は指定した同じ終端辺で一定。 -/
@[reassoc]
lemma simplexTerminalCospanFamily_right :
    simplexTerminalCospanFamily D s hs ≫ (pre horn₂₂.ι₀₂).app X =
      SSet.const (functorVertex s) :=
  stable_cospanFamilyOfArrows_left _ _ _

/-- cospan の上辺は元の全図式の同じ終端辺族。 -/
@[reassoc]
lemma simplexTerminalCospanFamily_top :
    simplexTerminalCospanFamily D s hs ≫ (pre horn₂₂.ι₁₂).app X =
      simplexTerminalArrowFamily D :=
  stable_cospanFamilyOfArrows_right _ _ _

private lemma columnCospan_right :
    horn₂₂.ι₀₂ ≫ pullbackCospan (squareColumnDiagram s) = s := by
  rw [pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge]
  simp only [squareColumnDiagram, ← Category.assoc, squareRightEdge, lift_snd,
    Category.id_comp]

private lemma columnCospan_top :
    horn₂₂.ι₁₂ ≫ pullbackCospan (squareColumnDiagram s) =
      SSet.const (s.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  rw [pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge]
  simp only [squareColumnDiagram, ← Category.assoc, squareTopEdge, lift_snd,
    SSet.const_comp]

/-- 最後の頂点では、元の同じ列四角形の cospan を厳密に回収する。 -/
lemma simplexTerminalCospanFamily_last :
    (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) :
      (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ simplexTerminalCospanFamily D s hs =
      SSet.const (functorVertex (pullbackCospan (squareColumnDiagram s))) := by
  apply stable_cospanFamily_hom_ext
  · rw [Category.assoc, simplexTerminalCospanFamily_right, SSet.comp_const, SSet.const_comp]
    change SSet.const (functorVertex s) =
      SSet.const (functorVertex (horn₂₂.ι₀₂ ≫ pullbackCospan (squareColumnDiagram s)))
    rw [columnCospan_right]
  · rw [Category.assoc, simplexTerminalCospanFamily_top, SSet.const_comp, SSet.const_comp]
    change SSet.const ((simplexTerminalArrowFamily D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (Fin.last n))) =
      SSet.const (functorVertex (horn₂₂.ι₁₂ ≫ pullbackCospan (squareColumnDiagram s)))
    rw [simplexTerminalArrowFamily_last, columnCospan_top, hs]

end SerrePositivity.InfinityCategories.Stable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospanFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalCospanFamily := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospanFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalCospanFamily_last := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospanFamily_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalCospanFamily_right := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospanFamily_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalCospanFamily_right_assoc := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospanFamily_right_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalCospanFamily_top := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospanFamily_top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalCospanFamily_top_assoc := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospanFamily_top_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalCospan_comm := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospan_comm

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalCospanFamily._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospanFamily._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalCospanFamily.congr_simp := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.simplexTerminalCospanFamily.congr_simp
