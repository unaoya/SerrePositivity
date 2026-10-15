module
public import SerrePositivity.DifferentialGraded.Bimodule.CochainComposition
public import SerrePositivity.DifferentialGraded.Complexes.CochainInterchange

/-! # uncurryHomの純粋斉次tensor上の合成保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma uncurryHom_forward_pure (M : Bimodule A B C)
    {x y z : DGTensorCategory A Bᵒᵖ C} {p q r s n : ℤ}
    (f₁ : GradedHom A x.1 y.1 p) (f₂ : GradedHom A x.2 y.2 q)
    (g₁ : GradedHom A y.1 z.1 r) (g₂ : GradedHom A y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    (M.uncurryHom x z).f n
        (forward A (dgTensorElement A f₁ f₂ rfl) (dgTensorElement A g₁ g₂ rfl) hn) =
      ((p + q) * (r + s)).negOnePow •
        ((M.uncurryHom x y).f (p + q) (dgTensorElement A f₁ f₂ rfl)).comp
          ((M.uncurryHom y z).f (r + s) (dgTensorElement A g₁ g₂ rfl)) hn := by
  have hm (k : ℤˣ) (t : GradedHom A x z n) :
      (M.uncurryHom x z).f n (k • t) = k • (M.uncurryHom x z).f n t := by
    simp only [Units.smul_def, map_zsmul]
  have he := cochain_quad_interchange
    (((M.rightAt x.2).map x.1 y.1).f p f₁) (M.leftCochain f₂ y.1.unop)
    (((M.rightAt y.2).map y.1 z.1).f r g₁) (M.leftCochain g₂ z.1.unop)
    (((M.rightAt x.2).map y.1 z.1).f r g₁) (M.leftCochain f₂ z.1.unop)
    (M.interchange (b := z.1.unop) (b' := y.1.unop) (c := x.2) (c' := y.2) g₁ f₂)
    (by omega : p + q + r + s = n)
  rw [dgTensor_forward, hm, uncurryHom_apply, uncurryHom_apply, uncurryHom_apply,
    rightCochain_forward, leftCochain_forward]
  simp only [Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul]
  rw [he]
  simp only [smul_smul, mul_assoc]
  have hs : (q * r).negOnePow *
      (((p + r) * (q + s)).negOnePow * ((q * s).negOnePow * (p * r).negOnePow)) =
      ((p + q) * (r + s)).negOnePow *
        ((r * s).negOnePow * ((p * q).negOnePow * (q * r).negOnePow)) := by
    simp only [← Int.negOnePow_add]
    congr 1
    ring
  exact congrArg (fun k : ℤˣ => k • _) hs

/-- uncurryHomは全Hom複体で豊穣合成を保存する。 -/
lemma uncurryHom_comp (M : Bimodule A B C) (x y z : DGTensorCategory A Bᵒᵖ C) :
    eComp (Complex A) x y z ≫ M.uncurryHom x z =
      (M.uncurryHom x y ⊗ₘ M.uncurryHom y z) ≫
        enrichedComposition (M.value x.1.unop x.2) (M.value y.1.unop y.2)
          (M.value z.1.unop z.2) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply SerrePositivity.cochainTensorQuad_hom_ext
    (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2)
    (y.1 ⟶[Complex A] z.1) (y.2 ⟶[Complex A] z.2) n
  intro p q r s hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_fourfold'
  intro f₁ f₂ g₁ g₂
  change (M.uncurryHom x z).f n
      (forward A (dgTensorElement A f₁ f₂ rfl) (dgTensorElement A g₁ g₂ rfl) (by omega)) =
    (enrichedComposition _ _ _).f n
      ((M.uncurryHom x y ⊗ₘ M.uncurryHom y z).f n
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) (p + q) (r + s) n (by omega)
          (dgTensorElement A f₁ f₂ rfl ⊗ₜ[A] dgTensorElement A g₁ g₂ rfl)))
  have hr := congrArg (fun t =>
    (enrichedComposition (M.value x.1.unop x.2) (M.value y.1.unop y.2)
      (M.value z.1.unop z.2)).f n t)
    (tensorMap_apply (M.uncurryHom x y) (M.uncurryHom y z) (p + q) (r + s) n (by omega)
      (dgTensorElement A f₁ f₂ rfl) (dgTensorElement A g₁ g₂ rfl))
  exact (M.uncurryHom_forward_pure f₁ f₂ g₁ g₂ (by omega)).trans
    (hr.trans (enrichedComposition_apply _ _ _ (p + q) (r + s) n (by omega) _ _)).symm

end SerrePositivity.DifferentialGraded.Bimodule
