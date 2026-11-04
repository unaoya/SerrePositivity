module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTargetContraction

/-!
分割で生成：docstring を書き直すこと
概要：cofiber の実右随伴の矢印の終域は、元の入力対象そのものである。
方針：四角形の共通角、右辺切断の厳密性、恒等矢印の始点評価を使う。
規約：全単体上の厳密な等式。使われ方：右随伴を零始点矢印として同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma cofiber_diagram_right_vertex (X : SSet.{u}) (z : (CofiberDiagrams.space X) _⦋0⦌) :
    (CofiberDiagrams.right X).app (Opposite.op ⦋0⦌) z =
      functorVertex (squareRightEdge ≫ squareDiagram z.val) := by
  have hz : functorVertex (squareDiagram z.val) = z.val :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change ((pre squareRightEdge).app X).app (Opposite.op ⦋0⦌) z.val = _
  rw [← hz]
  rfl

lemma cofiber_diagram_bottom_source (X : SSet.{u}) (z : (CofiberDiagrams.space X) _⦋0⦌) :
    (CofiberDiagrams.bottom X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) z =
        squareVertex (squareDiagram z.val) 0 0 := by
  have hz : functorVertex (squareDiagram z.val) = z.val :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change (evaluateFunctorAt _).app (Opposite.op ⦋0⦌)
    (((pre squareBottomEdge).app X).app (Opposite.op ⦋0⦌) z.val) = _
  rw [← hz]
  rfl

lemma cofiber_bottom_target_eq_right_source (X : SSet.{u}) :
    CofiberDiagrams.bottom X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      CofiberDiagrams.right X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  simp only [CofiberDiagrams.bottom, CofiberDiagrams.right, Category.assoc,
    stable_pre_evaluateFunctorAt]
  rfl

lemma identityArrow_source (X : SSet.{u}) :
    ArrowTarget.identityArrow X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      𝟙 X := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change X.map (𝟙 n) x = x
  exact CategoryTheory.Functor.map_id_apply X n x

end SerrePositivity.KST.LocalizingInvariants
