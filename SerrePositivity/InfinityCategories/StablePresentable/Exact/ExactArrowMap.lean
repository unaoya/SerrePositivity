module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorTerminal
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorInitial
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.Stable.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.ArrowStableExact

/-!
分割で生成：docstring を書き直すこと
概要：完全関手による矢印圏上の後合成も完全で、矢印の零性は両端の零性で判定できる。
方針：評価と後合成の厳密な交換を両端による完全性判定へ渡す。
規約：元の内部 Hom を保持。使われ方：点ごとの分母を安定な核の cofiber 分母に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.StablePresentable.Exact
open SerrePositivity.KST.LocalizingInvariants

lemma arrowMap_evaluation {X Y : SSet.{u}} (F : X ⟶ Y) (i : Fin 2) :
    (ihom (Δ[1] : SSet.{u})).map F ≫
        evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm i) =
      evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm i) ≫ F := rfl

def stableArrowCategory (A : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u} :=
  ⟨(ihom (Δ[1] : SSet.{u})).obj A.obj, inferInstance, inferInstance⟩

lemma arrowVertex_isZero_iff {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    IsZeroVertex v ↔ ∀ i : Fin 2, IsZeroVertex
      ((evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm i)).app (Opposite.op ⦋0⦌) v) := by
  constructor
  · intro hv i
    fin_cases i
    · exact IsExactFunctor.preservesZero
        (F := evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) _ hv
    · exact IsExactFunctor.preservesZero
        (F := evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) _ hv
  · intro hv
    obtain ⟨f, rfl⟩ := (functorVertexEquiv (Δ[1] : SSet.{u}) X).surjective v
    have hf : ∀ x : (Δ[1] : SSet.{u}) _⦋0⦌,
        IsZeroVertex (f.app (Opposite.op ⦋0⦌) x) := by
      intro x
      obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
      have hi := hv i
      change IsZeroVertex ((evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm i)).app
        (Opposite.op ⦋0⦌) (functorVertex f)) at hi
      rw [evaluateFunctorAt_functorVertex] at hi
      exact hi
    exact ⟨isInitialVertex_functorVertex_of_pointwise f (fun x => (hf x).1),
      isTerminalVertex_functorVertex_of_pointwise f (fun x => (hf x).2)⟩

end SerrePositivity.InfinityCategories.StablePresentable.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowMap_evaluation := _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.arrowMap_evaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowVertex_isZero_iff := _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.arrowVertex_isZero_iff

@[deprecated _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.stableArrowCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableArrowCategory := _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.stableArrowCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableArrowCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.stableArrowCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableArrowCategory._proof_2 := _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.stableArrowCategory._proof_2
