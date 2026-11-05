module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowFamilyHomotopy
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberSquareFamily

/-!
分割で生成：docstring を書き直すこと
概要：元の cofiber 全族の右辺を自然変換として保持する。
方針：右辺の prism を取り出し、零始点の場合の可逆性を各成分から示す。
規約：cofiber の比較を選び直さない。使われ方：C 随伴単位との同時比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
namespace SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

def rightArrow : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a ≫ (pre squareRightEdge).app X

lemma rightArrow_source : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow X a ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  conv_rhs => rw [← _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_bottom X a]
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

lemma rightArrow_target : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow X a ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X a := by
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow, Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

def rightHomotopy : SSet.Homotopy
    (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X a) where
  h := (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHomotopy (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow X a)).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHomotopy (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow X a)).h₀]
    exact congrArg (fun f => (SSet.RelativeMorphism.botEquiv.symm f).map)
      (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow_source X a)
  h₁ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHomotopy (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow X a)).h₁]
    exact congrArg (fun f => (SSet.RelativeMorphism.botEquiv.symm f).map)
      (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow_target X a)
  rel := (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHomotopy (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow X a)).rel

def rightHom : FunctorHom
    (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X a) :=
  Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy X a))

end SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightArrow := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightArrow_source := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightArrow_target := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightHom := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHom

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightHomotopy := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightArrow.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.rightHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy._proof_4
