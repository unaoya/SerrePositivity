module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.DiscreteEnrichmentFunctorEquiv
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# 元の自由圏の離散豊穣化からの関手の普遍性

概要：任意の豊穣目標への元の自由圏の関手は元の生成 quiver の像と同値である。
方針：元の離散豊穣化の比較と元の Paths.lift の普遍性を合成する。
規約：元の全対象・生成矢・射列を保持する。
使われ方：非指定自由部分と非指定生成矢の像の接続。
-/

@[expose] public section
universe u v uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeDiscreteEnrichment
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] {D : Type uD} [EnrichedCategory SSet.{max u v} D]

def pathFunctorEquiv {E : Type*} [Category E] : (Paths Q ⥤ E) ≃ (Q ⥤q E) where
  toFun F := Paths.of Q ⋙q F.toPrefunctor
  invFun := Paths.lift
  left_inv F := (Paths.lift_unique _ F rfl).symm
  right_inv := Paths.lift_spec

def functorEquiv :
    letI := DiscreteEnrichment.enrichedCategory (C := Paths Q)
    EnrichedFunctor SSet.{max u v} (Paths Q) D ≃ (Q ⥤q ForgetEnrichment SSet.{max u v} D) := by
  letI := DiscreteEnrichment.enrichedCategory (C := Paths Q)
  exact DiscreteEnrichment.functorEquiv.trans pathFunctorEquiv

end SerrePositivity.EInfinity.Hammock.FreeDiscreteEnrichment
