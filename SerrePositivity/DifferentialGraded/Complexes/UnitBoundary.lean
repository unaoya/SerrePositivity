module
public import SerrePositivity.DifferentialGraded.Complexes.Unit

/-! # 単位からのホモトピーと元の Hom 複体の境界 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- −1 の元 h を単位複体から K への −1 コチェインにする。 -/
def unitMinusOne (K : Complex A) (h : K.X (-1)) : Cochain (𝟙_ (Complex A)) K (-1) :=
  Cochain.mk (fun p q hpq =>
    if hp : p = 0 then
      eqToHom (by subst p; rfl) ≫
        ModuleCat.ofHom
          { toFun a := a • h
            map_add' a b := add_smul a b h
            map_smul' a b := mul_smul a b h } ≫
        eqToHom (congrArg K.X (show (-1 : ℤ) = q by omega))
    else 0)

/-- −1 コチェインを単位の 1 で評価すると境界の次数零元になる。 -/
lemma unit_homotopy_boundary (K : Complex A) (f g : 𝟙_ (Complex A) ⟶ K) :
    Nonempty (Homotopy f g) ↔
      ∃ h : K.X (-1), (K.d (-1) 0) h =
        (cycleFromUnit K f).val - (cycleFromUnit K g).val := by
  constructor
  · rintro ⟨h⟩
    refine ⟨h.hom 0 (-1) ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1), ?_⟩
    have hc := h.comm 0
    rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hc
    change f.f 0 =
      ((single (ModuleCat A) (.up ℤ) 0).obj (𝟙_ (ModuleCat A))).d 0 1 ≫ h.hom 1 0 +
        h.hom 0 (-1) ≫ K.d (-1) 0 + g.f 0 at hc
    rw [single_obj_d, zero_comp, zero_add] at hc
    have hv := congr($(hc).hom ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1))
    change f.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1) =
      K.d (-1) 0 (h.hom 0 (-1) ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1)) +
        g.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1) at hv
    change K.d (-1) 0 (h.hom 0 (-1) _) = f.f 0 _ - g.f 0 _
    rw [hv]
    abel
  · rintro ⟨h, dh⟩
    apply (unit_homotopy_iff K f g).2
    refine ⟨unitMinusOne K h, ?_⟩
    apply Cochain.ext₀
    intro p
    by_cases hp : p = 0
    · subst p
      rw [Cochain.add_v, Cochain.ofHom_v,
        δ_v (-1) 0 (by omega) (unitMinusOne K h) 0 0 (by omega) (-1) 1 rfl rfl]
      change f.f 0 = (unitMinusOne K h).v 0 (-1) rfl ≫ K.d (-1) 0 +
        (0 : ℤ).negOnePow •
          (((single (ModuleCat A) (.up ℤ) 0).obj (𝟙_ (ModuleCat A))).d 0 1 ≫
            (unitMinusOne K h).v 1 0 (by omega)) + g.f 0
      rw [single_obj_d, zero_comp, smul_zero, add_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change f.f 0 a = (K.d (-1) 0) ((show A from a) • h) + g.f 0 a
      rw [map_smul]
      have hd : (K.d (-1) 0) h = f.f 0 (1 : A) - g.f 0 (1 : A) := dh
      rw [hd, smul_sub, ← map_smul, ← map_smul]
      change f.f 0 a = f.f 0 ((show A from a) • (1 : A)) -
        g.f 0 ((show A from a) • (1 : A)) + g.f 0 a
      simp
    · apply (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) p hp).eq_of_src
end SerrePositivity.DifferentialGraded
