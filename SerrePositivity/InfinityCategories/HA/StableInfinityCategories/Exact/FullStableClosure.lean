module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberZeroSource
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare

/-!
分割で生成：docstring を書き直すこと
概要：零対象・fiber・cofiber に閉じた頂点条件の全部分圏は安定。
方針：周囲の指定 fiber/cofiber の四頂点の条件を確認し、双カルテジアンな実四角形を戻す。
規約：部分圏の安定性を入力しない。使われ方：通常 pullback の安定性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.FullSubcomplex
end SerrePositivity.KST.LocalizingInvariants.FullSubcomplex
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 周囲の実零三角形の cofiber と fiber に閉じる条件。 -/
structure StableVertexCondition {X : SSet.{u}} (P : X _⦋0⦌ → Prop) : Prop where
  zero (x) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x → P x
  cofiber (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t →
    P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0) → P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0) →
      P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1)
  fiber (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t →
    P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0) → P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1) →
      P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)

namespace FullSubcomplex
open _root_.SerrePositivity.KST.LocalizingInvariants.FullSubcomplex
variable {X : SSet.{u}} (P : X _⦋0⦌ → Prop)

/-- 頂点条件を部分複体の零単体にする。 -/
def vertex (x : X _⦋0⦌) (hx : P x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌ :=
  ⟨x, by intro v; have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
         subst v; simpa only [op_id, CategoryTheory.Functor.map_id_apply] using hx⟩

variable [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (hP : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition P)

include hP

variable {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌}
  (f : Truncated.Edge (X := (truncation 2).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})) x y)

omit [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] in
lemma cofiber_vertices
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι))) :
    ∀ i j : Fin 2, P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square i j) := by
  have hs : P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 0) := by
    rw [s.source_vertex]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
  have ht : P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 0) := by
    rw [s.target_vertex]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y
  intro i j
  fin_cases i <;> fin_cases j
  · exact hs
  · exact hP.zero _ s.zero_corner
  · exact ht
  · exact hP.cofiber s.toZeroTriangle s.isPushout hs ht

omit [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] in
lemma fiber_vertices
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι))) :
    ∀ i j : Fin 2, P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square i j) := by
  let g := f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 0 = x.val :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source s.square).symm.trans
      ((congrArg (fun r ↦ X.δ 1 (SSet.yonedaEquiv r)) s.right_edge).trans
        ((congrArg (X.δ 1) (SSet.yonedaEquiv.apply_symm_apply g.edge)).trans g.src_eq))
  have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 1 = y.val :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target s.square).symm.trans
      ((congrArg (fun r ↦ X.δ 0 (SSet.yonedaEquiv r)) s.right_edge).trans
        ((congrArg (X.δ 0) (SSet.yonedaEquiv.apply_symm_apply g.edge)).trans g.tgt_eq))
  have hp : P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 0) := by
    rw [hs]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
  have hq : P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 1) := by
    rw [ht]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y
  intro i j
  fin_cases i <;> fin_cases j
  · exact hP.fiber s.toZeroTriangle s.isPullback hp hq
  · exact hP.zero _ s.zero_corner
  · exact hp
  · exact hq

end FullSubcomplex
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableVertexCondition := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FullSubcomplex.cofiber_vertices := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.cofiber_vertices

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FullSubcomplex.fiber_vertices := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.fiber_vertices

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.vertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FullSubcomplex.vertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableVertexCondition.casesOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.casesOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableVertexCondition.cofiber := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.cofiber

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableVertexCondition.fiber := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.fiber

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableVertexCondition.mk := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableVertexCondition.rec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableVertexCondition.recOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableVertexCondition.zero := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FullSubcomplex.vertex._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.vertex._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableVertexCondition.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition.mk._flat_ctor
