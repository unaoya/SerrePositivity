module

public import SerrePositivity.InfinityCategories.F2.Ind.IndCommaCoconeComparison
public import SerrePositivity.InfinityCategories.F2.Ind.IndElementsLeftKanModel

/-!
概要：元の局所 Kan 普遍余錐を小さい元の圏へ制限すると、元の Indκ 密度余錐そのもの。
方針：前層内の同じ全余錐との比較を全部分包含の単射性で戻す。
規約：全余錐の射を厳密に同定し、頂点ごとの比較で代用しない。
使われ方：κ-filtered 保存関手の像の余極限性を標準 Kan 余錐へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の Yoneda comma 比較で制限した全余錐は、元の密度余錐の同じ全射。 -/
lemma presheafElementsYonedaSliceComparison_coconeMap {C : SSet.{u}} [Quasicategory C]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    joinMap (presheafElementsYonedaSliceComparison F) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (presheafYonedaSliceCocone F).val = (presheafDensityCocone F).val := by
  have h := congrArg Subtype.val (presheafElementsYonedaSliceComparison_cocone F)
  change sliceOverUncurry (presheafElementsYonedaSliceComparison F ≫ _) = _ at h
  rw [sliceOverUncurry_precomp] at h
  exact h

variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] (v : (IndInfinity κ C) _⦋0⦌)

/-- 元の指定 Indκ 密度余錐を周囲へ含めると、同じ前層の全密度余錐そのもの。 -/
lemma indVertexDensityCocone_val_inclusion :
    (indVertexDensityCocone κ v).val ≫ indInclusionPresheaf κ C =
      (presheafDensityCocone (indVertexPresheaf κ v)).val := by
  have h := congrArg Subtype.val (indDensityCocone_inclusion κ (indVertexPresheaf κ v)
    (indVertexPresheaf_mem κ v))
  exact h.trans (HomotopyLimits.coherentCoconeOfDiagramEq_val _ _)

/-- 小さい元の圏へ制限した同じ標準 Kan 余錐の全射は、元の Indκ 密度余錐そのもの。 -/
lemma indElementsLeftKanComparison_coconeMap :
    joinMap (indElementsLeftKanComparison κ v) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      slicePullbackCoconeMap (indYoneda κ C) (SSet.yonedaEquiv.symm v) =
        (indVertexDensityCocone κ v).val := by
  have : Mono (indInclusionPresheaf κ C) := inferInstanceAs
    (Mono (fullSubcomplexOnVertices (PresheafInfinity C) (IsIndVertex κ C)).ι)
  apply (cancel_mono (indInclusionPresheaf κ C)).mp
  simp only [indElementsLeftKanComparison, joinMap_comp_fixed, Category.assoc]
  have h := congrArg (fun f =>
    joinMap (presheafElementsYonedaSliceComparison (indVertexPresheaf κ v)) (𝟙 Δ[0]) ≫ f)
      (indLeftKanCommaIso_inv_coconeMap κ v)
  exact h.trans ((presheafElementsYonedaSliceComparison_coconeMap
    (indVertexPresheaf κ v)).trans (indVertexDensityCocone_val_inclusion κ v).symm)

end SerrePositivity.InfinityCategories.F2.Ind
