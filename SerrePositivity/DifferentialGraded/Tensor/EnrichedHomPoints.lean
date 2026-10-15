module
public import SerrePositivity.DifferentialGraded.Tensor.EnrichedHomAdjunction
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunction
public import SerrePositivity.DifferentialGraded.Module.TensorUnit

/-! # 豊穣tensor–Hom同型と閉零tensor–Hom随伴の一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A]

lemma curryRight_twice_unit {P Q S T : Complex A} (i : P ⊗ Q ⟶ S) (f : S ⟶ T) :
    curryRight (curryRight ((α_ (𝟙_ (Complex A)) P Q).hom ≫
      (((𝟙_ (Complex A)) ◁ i) ≫ uncurryRight (closedMap A f)))) =
      closedMap A (curryRight (i ≫ f)) := by
  rw [uncurryRight_closedMap]
  rw [leftUnitor_naturality_assoc, leftUnitor_tensor_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change curryRight (curryRight (((λ_ P).hom ⊗ₘ 𝟙 Q) ≫ (i ≫ f))) = _
  rw [curryRight_naturality_source, ← uncurryRight_closedMap, curryRight_uncurryRight]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 単位複体からの閉零射で豊穣同型を評価すると、先行する通常随伴の転置と一致する。 -/
lemma enrichedTensorHomEquiv_closedMap (M : ModuleCategory A D) (N : LeftModule A D)
    (T : Complex A) (f : obj A D (ForgetEnrichment.to (Complex A) M) N ⟶ T) :
    enrichedTensorHomEquiv A D (𝟙_ (Complex A)) (ForgetEnrichment.to (Complex A) M) N T
      (closedMap A f) =
    ForgetEnrichment.homTo (Complex A) (C := RightModule A D)
      (X := ForgetEnrichment.to (Complex A) M) (Y := homRightModule A D N T)
      (tensorHomEquiv A D M N T f) := by
  apply moduleHom_ext
  intro x
  rw [enrichedTensorHomEquiv_π]
  have h := moduleEvaluation_closedMap A D x (tensorHomEquiv A D M N T f)
  rw [tensorHomEquiv_eval] at h
  exact (curryRight_twice_unit A _ f).trans h

end SerrePositivity.DifferentialGraded.BalancedTensor
