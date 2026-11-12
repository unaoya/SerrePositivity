module
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! 単位からの指定次数 −1 cochain を、その値を変えず Hom 複体の境界元に取り出す。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded
variable {R : Type u} [CommRing R]

/-- 指定 cochain の次数零の単位の 1 への値。境界元を選び直さない。 -/
def dgGluingUnitCochainElement (K : Complex R) (h : Cochain (𝟙_ (Complex R)) K (-1)) :
    K.X (-1) :=
  (h.v 0 (-1) rfl) ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv 1)

/-- 指定 cochain の境界式は、同じ値を取った次数 −1 元の微分式になる。 -/
lemma dgGluingUnitCochainElement_boundary (K : Complex R)
    (h : Cochain (𝟙_ (Complex R)) K (-1)) (f : 𝟙_ (Complex R) ⟶ K)
    (hh : δ (-1) 0 h = Cochain.ofHom f) :
    (K.d (-1) 0) (dgGluingUnitCochainElement K h) = (cycleFromUnit K f).val := by
  have hc := Cochain.congr_v hh 0 0 (add_zero 0)
  rw [δ_v (-1) 0 (by omega) h 0 0 (by omega) (-1) 1 rfl rfl, Cochain.ofHom_v] at hc
  change (h.v 0 (-1) rfl) ≫ K.d (-1) 0 + (0 : ℤ).negOnePow •
    (((single (ModuleCat R) (ComplexShape.up ℤ) 0).obj (𝟙_ (ModuleCat R))).d 0 1 ≫
      h.v 1 0 (by omega)) = f.f 0 at hc
  rw [single_obj_d, zero_comp, smul_zero, add_zero] at hc
  exact congrArg (fun a => a
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv 1)) hc

/-- 鎖写像による cochain の移送は、この指定元の同じ次数の像を取ることと一致。 -/
lemma dgGluingUnitCochainElement_postcompose {K L : Complex R}
    (h : Cochain (𝟙_ (Complex R)) K (-1)) (f : K ⟶ L) :
    dgGluingUnitCochainElement L (h.comp (Cochain.ofHom f) (add_zero (-1))) =
      f.f (-1) (dgGluingUnitCochainElement K h) := by
  simp only [dgGluingUnitCochainElement, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    ModuleCat.comp_apply]

/-- 同じ指定 cochain を同型の逆で移して戻すと、元の同じ境界元の像を回収する。 -/
lemma dgGluingUnitCochainElement_iso {K L P : Complex R}
    (h : Cochain (𝟙_ (Complex R)) K (-1)) (f : K ⟶ L) (e : P ≅ L) :
    e.hom.f (-1)
      (dgGluingUnitCochainElement P (h.comp (Cochain.ofHom (f ≫ e.inv)) (add_zero (-1)))) =
      f.f (-1) (dgGluingUnitCochainElement K h) := by
  rw [dgGluingUnitCochainElement_postcompose]
  have he : (f ≫ e.inv) ≫ e.hom = f := by simp
  exact congrArg (fun a => a.f (-1) (dgGluingUnitCochainElement K h)) he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
