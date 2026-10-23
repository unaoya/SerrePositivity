module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationGlue
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCornerMap

/-!
概要：補間族の元の試験形状への制限は、同じ slice 円柱の補間領域上の制限。
方針：円柱と始点余錐の両脚で元の厳密な境界式を使う。
規約：元の全 slice 族を保持。使われ方：再構成全円柱との厳密な照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の slice 円柱の始点式を、同じ定値始点包含で読む。 -/
lemma indArrowSlicePrism_start_ι₀ {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
    {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
    {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
    (W : IndArrowSlicePrism κ D q H) :
    SSet.ι₀ ≫ W.val = indArrowSourceSliceLift κ D H := by
  let s : join T (Δ[0] : SSet.{u + 1}) ⟶ join T Δ[0] ⊗ Δ[0] :=
    lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  have hs : s ≫ (join T (Δ[0] : SSet.{u + 1}) ◁ stdSimplex.δ 1) = SSet.ι₀ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    rfl
  have h := congrArg (fun z ↦ s ≫ z) W.start
  calc
    _ = (s ≫ (join T (Δ[0] : SSet.{u + 1}) ◁ stdSimplex.δ 1)) ≫ W.val :=
      congrArg (fun z ↦ z ≫ W.val) hs.symm
    _ = (s ≫ fst _ _) ≫ indArrowSourceSliceLift κ D H := by
      simpa only [Category.assoc] using h
    _ = _ := by rw [show s ≫ fst _ _ = 𝟙 _ from lift_fst _ _, Category.id_comp]

variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)

/-- 同じ補間全族の制限は、元の slice 円柱の同じ補間領域への制限そのもの。 -/
lemma indArrowInterpolationGlue_restrict :
    arrowInterpolationCornerMap ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0])) ≫
      indArrowInterpolationGlue V =
        arrowInterpolationCornerInclusion ((SSet.uliftFunctor.{u + 1, u}).obj A) ≫
          V.slicePrism.val := by
  apply pushout.hom_ext
  · simp only [← Category.assoc, arrowInterpolationCornerMap_old,
      arrowInterpolationCornerInclusion_old]
    rw [Category.assoc, indArrowInterpolationGlue_old, indArrowInterpolationSliceCylinder_old]
  · simp only [← Category.assoc, arrowInterpolationCornerMap_source,
      arrowInterpolationCornerInclusion_source]
    rw [Category.assoc, indArrowInterpolationGlue_source, indArrowSourceSliceLift_precomp,
      indArrowSlicePrism_start_ι₀]

end SerrePositivity.InfinityCategories.F2.Ind
