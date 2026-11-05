module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
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
public import Mathlib.CategoryTheory.Functor.FunctorHom
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTargetContraction

/-!
分割で生成：docstring を書き直すこと
概要：矢印圏の元の終点評価は恒等矢印関手の実左随伴。
方針：max による収縮の前後合成を厳密に計算し、h Fun 全体の三角恒等式へ渡す。
規約：始域に安定性を要求しない。使われ方：cofiber 回転を経た Cone の実右随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ArrowTarget
end SerrePositivity.KST.LocalizingInvariants.ArrowTarget
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget
open SerrePositivity.KST.LocalizingInvariants.ArrowTarget

variable (X : SSet.{u})

lemma contraction_target : contraction X ≫ target X =
    fst (arrows X) (Δ[1] : SSet.{u}) ≫ target X := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨f, t⟩
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app intervalMax_left_one (Opposite.op ⦋n⦌)) t
  change intervalMax.app _ (PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n, t) =
    PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n at h
  change f.app (Opposite.op ⦋n⦌) (𝟙 _) (intervalMax.app _
    (PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n, t)) =
      f.app _ (𝟙 _) (PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n)
  rw [h]

lemma identityArrow_contraction : (identityArrow X ▷ (Δ[1] : SSet.{u})) ≫ contraction X =
    fst X (Δ[1] : SSet.{u}) ≫ identityArrow X := by
  apply uncurry_injective
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.contraction, uncurry_curry, uncurry_natural_left]
  change _ = (Δ[1] ◁ fst X (Δ[1] : SSet.{u})) ≫ uncurry (constantFunctorMap Δ[1] X)
  rw [constantFunctorMap, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨i, x, t⟩
  change X.map (𝟙 (Opposite.op ⦋n⦌)) x = x
  exact CategoryTheory.Functor.map_id_apply X _ x

def unitHomotopy : SSet.Homotopy (𝟙 (arrows X)) (target X ≫ identityArrow X) where
  h := contraction X
  h₀ := contraction_zero X
  h₁ := contraction_one X
  rel := by ext n ⟨x, y⟩; exact x.property.elim

end SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.contraction_target := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget.contraction_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.identityArrow_contraction := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget.identityArrow_contraction

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget.unitHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.unitHomotopy := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget.unitHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.unitHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget.unitHomotopy._proof_1
