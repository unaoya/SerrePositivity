module

public import SerrePositivity.KST.Spectra.IntervalBoundary
public import SerrePositivity.KST.Spectra.BoundaryTensorExt
public import SerrePositivity.Spectra.Pointed.TensorCoproduct

/-!
概要：二つの指定パラメータ族を、区間の両端境界上の同じ実パラメータ族へ束ねる。
方針：端点余積と境界の同型を使い、直積した余積の二成分へ元の族をそのまま貼る。
規約：終点・始点の順序を保持。使われ方：上下の指定三角形を保つ正方形の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra
variable {T E : SSet.{u}} (f₀ f₁ : T ⟶ E)

/-- 始点・終点の二つの元の族を、同じ境界上の族へ束ねる。 -/
def intervalBoundaryFamily : (∂Δ[1] : SSet.{u}) ⊗ T ⟶ E :=
  (asIso intervalBoundaryMap.{u}).inv ▷ T ≫
    PointedObject.tensorRightDesc ((λ_ T).hom ≫ f₁) ((λ_ T).hom ≫ f₀)

/-- 端点余積へ戻すと、元の二つの指定族そのものを貼った族になる。 -/
lemma intervalBoundaryFamily_map : intervalBoundaryMap.{u} ▷ T ≫
    intervalBoundaryFamily f₀ f₁ =
      PointedObject.tensorRightDesc ((λ_ T).hom ≫ f₁) ((λ_ T).hom ≫ f₀) := by
  have h : intervalBoundaryMap.{u} ≫ (asIso intervalBoundaryMap).inv = 𝟙 _ :=
    (asIso intervalBoundaryMap).hom_inv_id
  rw [intervalBoundaryFamily, ← comp_whiskerRight_assoc, h,
    id_whiskerRight, Category.id_comp]

/-- 終点の余積成分へ制限すると元の終点族。 -/
lemma intervalBoundaryFamily_inl :
    ((coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫
      intervalBoundaryMap) ▷ T ≫ intervalBoundaryFamily f₀ f₁ = (λ_ T).hom ≫ f₁ := by
  rw [comp_whiskerRight_assoc, intervalBoundaryFamily_map, PointedObject.tensorRightDesc_inl]

/-- 始点の余積成分へ制限すると元の始点族。 -/
lemma intervalBoundaryFamily_inr :
    ((coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫
      intervalBoundaryMap) ▷ T ≫ intervalBoundaryFamily f₀ f₁ = (λ_ T).hom ≫ f₀ := by
  rw [comp_whiskerRight_assoc, intervalBoundaryFamily_map, PointedObject.tensorRightDesc_inr]

/-- 境界の零番目の面は、端点余積の終点成分そのもの。 -/
lemma intervalBoundary_face_zero : boundary.ι.{u} (0 : Fin 2) =
    PointedSimplicialSet.deltaZeroUnitIso.hom ≫
      ((coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫
        intervalBoundaryMap) := by
  apply (cancel_mono (boundary 1).ι).1
  rw [boundary.ι_ι, Category.assoc, Category.assoc, intervalBoundaryMap_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl, SSet.comp_const, stdSimplex.δ_zero_eq_const]

/-- 境界の一番目の面も、端点余積の始点成分そのもの。 -/
lemma intervalBoundary_face_one : boundary.ι.{u} (1 : Fin 2) =
    PointedSimplicialSet.deltaZeroUnitIso.hom ≫
      ((coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫
        intervalBoundaryMap) := by
  apply (cancel_mono (boundary 1).ι).1
  rw [boundary.ι_ι, Category.assoc, Category.assoc, intervalBoundaryMap_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr, SSet.comp_const, stdSimplex.δ_one_eq_const]

/-- 境界族を終点の面へ制限すると元の終点族。 -/
lemma intervalBoundaryFamily_zero : boundary.ι (0 : Fin 2) ▷ T ≫
    intervalBoundaryFamily f₀ f₁ = snd (Δ[0] : SSet.{u}) T ≫ f₁ := by
  rw [intervalBoundary_face_zero, comp_whiskerRight_assoc, intervalBoundaryFamily_inl]
  rfl

/-- 境界族を始点の面へ制限すると元の始点族。 -/
lemma intervalBoundaryFamily_one : boundary.ι (1 : Fin 2) ▷ T ≫
    intervalBoundaryFamily f₀ f₁ = snd (Δ[0] : SSet.{u}) T ≫ f₀ := by
  rw [intervalBoundary_face_one, comp_whiskerRight_assoc, intervalBoundaryFamily_inr]
  rfl

/-- パラメータの制限は、同じ二つの元の族の制限を束ねる操作と厳密に可換。 -/
lemma intervalBoundaryFamily_pre {S : SSet.{u}} (a : S ⟶ T) :
    (∂Δ[1] : SSet.{u}) ◁ a ≫ intervalBoundaryFamily f₀ f₁ =
      intervalBoundaryFamily (a ≫ f₀) (a ≫ f₁) := by
  apply boundary_tensor_hom_ext
  intro j
  fin_cases j
  · change boundary.ι (0 : Fin 2) ▷ S ≫
        ((∂Δ[1] : SSet.{u}) ◁ a ≫ intervalBoundaryFamily f₀ f₁) =
      boundary.ι (0 : Fin 2) ▷ S ≫ intervalBoundaryFamily (a ≫ f₀) (a ≫ f₁)
    rw [← whisker_exchange_assoc, intervalBoundaryFamily_zero, intervalBoundaryFamily_zero,
      whiskerLeft_snd_assoc]
  · change boundary.ι (1 : Fin 2) ▷ S ≫
        ((∂Δ[1] : SSet.{u}) ◁ a ≫ intervalBoundaryFamily f₀ f₁) =
      boundary.ι (1 : Fin 2) ▷ S ≫ intervalBoundaryFamily (a ≫ f₀) (a ≫ f₁)
    rw [← whisker_exchange_assoc, intervalBoundaryFamily_one, intervalBoundaryFamily_one,
      whiskerLeft_snd_assoc]

end SerrePositivity.KST.Spectra
