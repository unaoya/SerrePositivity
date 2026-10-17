module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedLocalizingGeneration
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # 恒等関手からのshift整合的自然変換の同型性の閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (G : DerivedModuleCategory A D ⥤ DerivedModuleCategory A D)
variable (α : 𝟭 (DerivedModuleCategory A D) ⟶ G)

def derivedNatTransIsoLocus : ObjectProperty (DerivedModuleCategory A D) :=
  fun X => IsIso (α.app X)

instance derivedNatTransIsoLocus_closedIso :
    (derivedNatTransIsoLocus A D G α).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    change IsIso (α.app _) at hX ⊢
    let := hX
    have he : α.app _ = e.inv ≫ α.app _ ≫ G.map e.hom := by
      rw [← α.naturality]
      simp
    rw [he]
    infer_instance

variable [G.CommShift ℤ] [G.IsTriangulated] [G.Additive] [NatTrans.CommShift α ℤ]

instance derivedNatTransIsoLocus_shift :
    (derivedNatTransIsoLocus A D G α).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro X hX
    change IsIso (α.app X) at hX
    let := hX
    change IsIso (α.app (X⟦n⟧))
    rw [NatTrans.app_shift α]
    infer_instance⟩

instance derivedNatTransIsoLocus_containsZero :
    (derivedNatTransIsoLocus A D G α).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    change IsIso (α.app 0)
    exact (isZero_zero _).isIso (G.map_isZero (isZero_zero _)) _⟩

instance derivedNatTransIsoLocus_closedTriangle :
    (derivedNatTransIsoLocus A D G α).IsTriangulatedClosed₃ := by
  apply ObjectProperty.IsTriangulatedClosed₃.mk'
  intro T hT h₁ h₂
  change IsIso (α.app T.obj₁) at h₁
  change IsIso (α.app T.obj₂) at h₂
  change IsIso (α.app T.obj₃)
  let φ : T ⟶ G.mapTriangle.obj T := {
    hom₁ := α.app T.obj₁
    hom₂ := α.app T.obj₂
    hom₃ := α.app T.obj₃
    comm₁ := α.naturality T.mor₁
    comm₂ := α.naturality T.mor₂
    comm₃ := by
      dsimp
      rw [← α.naturality_assoc, ← NatTrans.shift_app_comm]
      simp }
  exact isIso₃_of_isIso₁₂ φ hT (G.map_distinguished T hT) h₁ h₂

instance derivedNatTransIsoLocus_triangulated :
    (derivedNatTransIsoLocus A D G α).IsTriangulated where
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

omit [G.CommShift ℤ] [G.IsTriangulated] [G.Additive] [NatTrans.CommShift α ℤ] in
lemma derivedNatTransIsoLocus_coproduct {J : Type u}
    (F : J → DerivedModuleCategory A D) [PreservesColimit (Discrete.functor F) G]
    (hF : ∀ j, derivedNatTransIsoLocus A D G α (F j)) :
    derivedNatTransIsoLocus A D G α (∐ F) := by
  let (j : J) : IsIso (α.app (F j)) := hF j
  have h : Limits.Sigma.map (fun j => α.app (F j)) ≫ sigmaComparison G F = α.app (∐ F) := by
    apply Sigma.hom_ext
    intro j
    simp only [Limits.Sigma.ι_map_assoc, ι_comp_sigmaComparison]
    exact (α.naturality (Sigma.ι F j)).symm
  change IsIso (α.app (∐ F))
  rw [← h]
  infer_instance

end SerrePositivity.DifferentialGraded
