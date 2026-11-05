module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
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
public import SerrePositivity.InfinityCategories.Core.CoconeFamily
public import SerrePositivity.InfinityCategories.Core.ConeFamily
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.LimitConeFamilies
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.RelativeInitialBoundary
public import SerrePositivity.InfinityCategories.Core.RelativeInitialVertices
public import SerrePositivity.InfinityCategories.Core.RelativeTerminalExtension
public import SerrePositivity.InfinityCategories.Core.Square
public import SerrePositivity.InfinityCategories.Core.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Core.ZeroTargetArrows
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.F1.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.ZeroSourceArrows

/-!
分割で生成：docstring を書き直すこと
概要：普遍 cofiber 四角形の全部分圏と底辺・右辺の評価。
方針：元の四角形の零角と押し出し条件を保持し、安定性で普遍錐の族も得る。
規約：選択済みの全 cofiber 族もこの全部分圏へ入る。使われ方：cofiber 回転の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
namespace SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams
open SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams

def Predicate {X : SSet.{u}} (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  IsZeroVertex (squareVertex (squareDiagram v) 0 1) ∧ IsPushoutSquare (squareDiagram v)

def space (X : SSet.{u}) : SSet.{u} :=
  (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.Predicate : SSet.{u})

instance instQuasicategorySpace (X : SSet.{u}) [Quasicategory X] : Quasicategory (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X) :=
  fullSubcomplexOnVertices_quasicategory _ _

def inclusion (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
  (fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.Predicate).ι

def bottom (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre squareBottomEdge).app X

def right (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre squareRightEdge).app X

def left (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X ⟶ zeroTargetArrows X :=
  fullSubcomplexLift IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre squareLeftEdge).app X) (by
    intro v
    have hv := (fullSubcomplexOnVertices_vertex v).1
    have he : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change IsZeroTargetArrow (((pre squareLeftEdge).app X).app _ v.val)
    rw [← he]
    change IsZeroTargetArrow (functorVertex (squareLeftEdge ≫ squareDiagram v.val))
    unfold IsZeroTargetArrow
    rw [evaluateFunctorAt_functorVertex]
    exact hv)

def top (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X ⟶ zeroSourceArrows X :=
  fullSubcomplexLift IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre squareTopEdge).app X) (by
    intro v
    have hv := (fullSubcomplexOnVertices_vertex v).1
    have he : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change IsZeroSourceArrow (((pre squareTopEdge).app X).app _ v.val)
    rw [← he]
    change IsZeroSourceArrow (functorVertex (squareTopEdge ≫ squareDiagram v.val))
    unfold IsZeroSourceArrow
    rw [evaluateFunctorAt_functorVertex]
    exact hv)

def cocones (X : SSet.{u}) [Quasicategory X] : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X ⟶ colimitCocones (horn 2 0 : SSet.{u}) X :=
  fullSubcomplexLift (InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) X))
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre spanCoconeSquareIso.hom).app X) (by
    intro v
    have hp := (fullSubcomplexOnVertices_vertex v).2
    have he : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change InitialBoundaryLifting _ (((pre spanCoconeSquareIso.hom).app X).app _ v.val)
    rw [← he]
    exact hp.initialBoundaryLifting)

lemma cocones_inclusion (X : SSet.{u}) [Quasicategory X] : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones X ≫
    (relativeInitialVertices (coconeRestriction (horn 2 0 : SSet.{u}) X)).ι =
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre spanCoconeSquareIso.hom).app X := rfl

lemma cocones_projection (X : SSet.{u}) [Quasicategory X] : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones X ≫
    colimitCoconeProjection (horn 2 0 : SSet.{u}) X =
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre spanSquareBoundary).app X := by
  change (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones X ≫ (relativeInitialVertices (coconeRestriction _ X)).ι) ≫
    (pre (joinInl _ Δ[0])).app X = _
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones_inclusion, Category.assoc, ← NatTrans.comp_app, ← pre_map]
  rfl

def cones (X : SSet.{u}) [Quasicategory X] [IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X ⟶ limitCones (horn 2 2 : SSet.{u}) X :=
  fullSubcomplexLift (TerminalBoundaryLifting (coneRestriction (horn 2 2 : SSet.{u}) X))
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre cospanConeSquareIso.hom).app X) (by
    intro v
    have hv := fullSubcomplexOnVertices_vertex v
    have hp := IsStable.pullback_of_pushout (⟨squareDiagram v.val, hv.1⟩ : ZeroTriangle X) hv.2
    have he : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change TerminalBoundaryLifting _ (((pre cospanConeSquareIso.hom).app X).app _ v.val)
    rw [← he]
    exact terminalBoundaryLifting_coneRestriction_of_isLimitCone
      (pullbackCone (squareDiagram v.val)) hp)

lemma cones_inclusion (X : SSet.{u}) [Quasicategory X] [IsStable X] : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cones X ≫
    (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι =
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre cospanConeSquareIso.hom).app X := rfl

lemma cones_projection (X : SSet.{u}) [Quasicategory X] [IsStable X] : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cones X ≫
    limitConeProjection (horn 2 2 : SSet.{u}) X =
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre cospanSquareBoundary).app X := by
  change (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cones X ≫ (relativeTerminalVertices (coneRestriction _ X)).ι) ≫
    (pre (joinInr Δ[0] _)).app X = _
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cones_inclusion, Category.assoc, ← NatTrans.comp_app, ← pre_map]
  rfl

end SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.Predicate (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.Predicate := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.Predicate

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.bottom := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.cocones := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.cocones_inclusion := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones_inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.cocones_projection := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones_projection

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cones (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.cones := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cones

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.cones_inclusion := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cones_inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.cones_projection := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cones_projection

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.inclusion := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.instQuasicategorySpace (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.instQuasicategorySpace := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.instQuasicategorySpace

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.left (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.left := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.left

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.right := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.space := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.top (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.top := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.Predicate._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.Predicate._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.cocones._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.cocones._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cocones._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.cones._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.cones._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.left._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.left._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.top._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.top._proof_1
