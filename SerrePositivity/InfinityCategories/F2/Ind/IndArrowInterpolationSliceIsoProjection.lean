module

public import
  SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationOldFamilyRelativeSliceIso
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeFunctorVertexIsoProjection
/-!
概要：元の補間族と q の slice 同型は、始点評価後に元の等号の同型へ戻る。
方針：既存の相対同型を包含で写し、その同じ像の後合成を計算する。
規約：両端の全族と評価後の同型を保持。使われ方：実 comma への相対反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
local notation "p" => SSet.yonedaEquiv.symm (functorVertex D)
local notation "e" => evaluateFunctorAt (Y := IndInfinity κ C)
  (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
local notation "f" => indArrowInterpolationOldFamily V ≫ diagramCommaSliceProjection κ D
local notation "g" => q ≫ diagramCommaSliceProjection κ D
/-- 概要：元の slice 同型を、指定始点評価の元の等号同型との一致付きで選べる。
方針：相対同型の包含後の射影を計算する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma exists_indArrowInterpolationOldFamily_slice_iso_projection :
    ∃ (h : f ≫ sliceOverPostcomp p e = g ≫ sliceOverPostcomp p e)
      (d : FunctorIso f g),
      d.postcomp (sliceOverPostcomp p e) = eqToIso (congrArg
        (fun v => SSet.HomotopyCategory.mk (functorVertex v)) h) := by
  obtain ⟨h, ⟨d⟩⟩ := exists_indArrowInterpolationOldFamily_relative_slice_iso V
  refine ⟨h, relativeFunctorVertexIsoImage _ _ f g h rfl d, ?_⟩
  exact relativeFunctorVertexIsoImage_postcomp _ _ f g h rfl d
end SerrePositivity.InfinityCategories.F2.Ind
