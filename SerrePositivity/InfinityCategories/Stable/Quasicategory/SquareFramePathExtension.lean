module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrameBoundary
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrameFunctoriality

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
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame
open SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame
variable {X : SSet.{u}} [Quasicategory X] (f : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame (equivalencePath X))
  (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
  (hf : (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.postcomp f) (equivalencePathEndpoint X 0) = _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare Q)

structure PathExtension where
  family : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ equivalencePath X
  source : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.family ≫ equivalencePathEndpoint X 0 = Q
  boundary : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.family = f.diagram

include hf in
lemma pathExtension_nonempty : Nonempty (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension f Q) := by
  have he : f.diagram ≫ equivalencePathEndpoint X 0 = _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ Q := by
    rw [_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.diagram_postcomp, hf, _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.diagram_ofSquare]
  let sq : CommSq f.diagram _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι (equivalencePathEndpoint X 0) Q := ⟨he⟩
  have : HasLiftingProperty _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι (equivalencePathEndpoint X 0) :=
    TrivialKanFibration.mem (p := equivalencePathEndpoint X 0) _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι inferInstance
  exact ⟨⟨sq.lift, sq.fac_right, sq.fac_left⟩⟩

def pathExtension : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension f Q := (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.pathExtension_nonempty f Q hf).some

namespace PathExtension
open SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension
variable {f Q} (w : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension f Q)

def target : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X := w.family ≫ equivalencePathEndpoint X 1

omit [Quasicategory X] in
lemma target_boundary : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ w.target =
    ((_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.postcomp f) (equivalencePathEndpoint X 1)).diagram := by
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.target, ← Category.assoc, w.boundary, _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.diagram_postcomp]

end PathExtension
end SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.pathExtension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.pathExtension := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.pathExtension

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.pathExtension_nonempty := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.pathExtension_nonempty

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension._sizeOf_inst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.boundary := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.family (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.family := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.family

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.rec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.source := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.source

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.target (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.target := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.target_boundary := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.target_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.pathExtension._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.pathExtension._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.target.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.target.eq_1
