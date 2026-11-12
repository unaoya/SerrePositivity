module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrameBoundary
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquareFrameFunctoriality

/-!
分割で生成：docstring を書き直すこと
概要：元の正方形の境界に指定された四辺の可逆 path を、正方形全体へ延長する。
方針：path の始点評価の自明 Kan 性と境界の単射性を使う。
規約：指定した境界 path は厳密に保持。使われ方：元の BF 合成射への四辺の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareFrame
end SerrePositivity.KST.LocalizingInvariants.SquareFrame
namespace SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension
end SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {X : SSet.{u}} [Quasicategory X] (f : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X))
  (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
  (hf : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.postcomp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare Q)

structure PathExtension where
  family : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X
  source : family ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = Q
  boundary : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ family = f.diagram

include hf in
lemma pathExtension_nonempty : Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension f Q) := by
  have he : f.diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ Q := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.diagram_postcomp, hf, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.diagram_ofSquare]
  let sq : CommSq f.diagram _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) Q := ⟨he⟩
  have : HasLiftingProperty _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι inferInstance
  exact ⟨⟨sq.lift, sq.fac_right, sq.fac_left⟩⟩

def pathExtension : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension f Q := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.pathExtension_nonempty f Q hf).some

namespace PathExtension
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {f Q} (w : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension f Q)

def target : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X := w.family ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1

omit [Quasicategory X] in
lemma target_boundary : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame.boundaryι ≫ w.target =
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.postcomp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1)).diagram := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.target, ← Category.assoc, w.boundary, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.diagram_postcomp]

end PathExtension
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.pathExtension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.pathExtension := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.pathExtension

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.pathExtension_nonempty := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.pathExtension_nonempty

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension._sizeOf_inst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.boundary := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.casesOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.ctorIdx := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.family (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.family := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.family

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.noConfusionType := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.rec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.recOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.source := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.source

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.target (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.target := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.target_boundary := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.target_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.pathExtension._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.pathExtension._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk.inj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk.injEq := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.target.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension.target.eq_1
