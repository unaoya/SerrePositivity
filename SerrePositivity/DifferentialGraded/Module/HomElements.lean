module
public import SerrePositivity.DifferentialGraded.Module.Action
public import SerrePositivity.DifferentialGraded.Complexes.DiskGenerator

/-! # 主Hom endの斉次要素の構成

全次数で自然なcochain族を、diskの生成元とequalizerの普遍性からendへ入れる。
cycle条件は課さない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

lemma moduleParamRelationLeft_apply {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (x y : Dᵒᵖ) (k p : ℤ) (t : K.X k) (f : GradedHom A x y p) :
    ((curryRight ((β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _)).f k t).v p (k + p) (by omega) f =
      ((M.map x y).f p f).comp ((σ y).f k t) (by omega : p + k = k + p) := by
  change (enrichedComposition _ _ _).f (k + p)
    ((M.map x y ⊗ₘ σ y).f (k + p)
      ((signedSwap K (x ⟶[Complex A] y)).hom.f (k + p)
        (ιTensorObj K (x ⟶[Complex A] y) k p (k + p) rfl (t ⊗ₜ[A] f)))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (k * p).negOnePow • (enrichedComposition _ _ _).f (k + p)
    ((M.map x y ⊗ₘ σ y).f (k + p)
      (ιTensorObj (x ⟶[Complex A] y) K p k (k + p) (by omega) (f ⊗ₜ[A] t))) = _
  rw [tensorMap_apply, enrichedComposition_apply, mul_comm p k, smul_smul,
    Int.units_mul_self, one_smul]

lemma moduleParamRelationRight_apply {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (x y : Dᵒᵖ) (k p : ℤ) (t : K.X k) (f : GradedHom A x y p) :
    ((curryRight ((σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _)).f k t).v
        p (k + p) (by omega) f =
      (k * p).negOnePow • (((σ x).f k t).comp ((N.map x y).f p f) rfl) := by
  change (enrichedComposition _ _ _).f (k + p)
    ((σ x ⊗ₘ N.map x y).f (k + p)
      (ιTensorObj K (x ⟶[Complex A] y) k p (k + p) rfl (t ⊗ₜ[A] f))) = _
  rw [tensorMap_apply, enrichedComposition_apply]

abbrev moduleHomDiskFamily {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q) (x : Dᵒᵖ) :
    complexDisk A q ⟶ homComplex A (M.obj x) (N.obj x) :=
  (complexDiskHomEquiv A _ q).symm (h x)

lemma moduleHomDiskFamily_naturality {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q)
    (hn : ∀ (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p),
      ((M.map x y).f p f).comp (h y) (by omega : p + q = q + p) =
        (q * p).negOnePow • ((h x).comp ((N.map x y).f p f) rfl)) (x y : Dᵒᵖ) :
    curryRight ((β_ (complexDisk A q) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ moduleHomDiskFamily A q h y) ≫ enrichedComposition _ _ _) =
    curryRight ((moduleHomDiskFamily A q h x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _) := by
  apply (complexDiskHomEquiv A _ q).injective
  rw [complexDiskHomEquiv_apply, complexDiskHomEquiv_apply]
  change (curryRight _).f q ((complexDiskX₀ A q).inv (1 : A)) =
    (curryRight _).f q ((complexDiskX₀ A q).inv (1 : A))
  apply Cochain.ext
  intro p n hpn
  obtain rfl : n = q + p := by omega
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  let σ := fun z : Dᵒᵖ =>
    (complexDiskHomEquiv A (homComplex A (M.obj z) (N.obj z)) q).symm (h z)
  have hL := moduleParamRelationLeft_apply A (M := M) (N := N) σ x y
    q p ((complexDiskX₀ A q).inv (1 : A)) f
  have hR := moduleParamRelationRight_apply A (M := M) (N := N) σ x y
    q p ((complexDiskX₀ A q).inv (1 : A)) f
  have hg (z : Dᵒᵖ) :=
    complexDiskHomEquiv_symm_generator A (homComplex A (M.obj z) (N.obj z)) q (h z)
  refine hL.trans (Eq.trans ?_ hR.symm)
  change ((M.map x y).f p f).comp
      (((complexDiskHomEquiv A (homComplex A (M.obj y) (N.obj y)) q).symm (h y)).f q
        ((complexDiskX₀ A q).inv (1 : A)))
      (by omega : p + q = q + p) =
    (q * p).negOnePow •
      ((((complexDiskHomEquiv A (homComplex A (M.obj x) (N.obj x)) q).symm (h x)).f q
        ((complexDiskX₀ A q).inv (1 : A))).comp
        ((N.map x y).f p f) rfl)
  rw [hg, hg]
  exact hn x y p f

variable (D) [Small.{u} D]

def moduleHomElementFamilyMap {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q) :
    complexDisk A q ⟶ homCandidates A D M N :=
  Pi.lift (fun x => (complexDiskHomEquiv A (homComplex A (M.obj (op x)) (N.obj (op x))) q).symm
    (h (op x)))

lemma moduleHomElementFamilyMap_condition {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q)
    (hn : ∀ (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p),
      ((M.map x y).f p f).comp (h y) (by omega : p + q = q + p) =
        (q * p).negOnePow • ((h x).comp ((N.map x y).f p f) rfl)) :
    moduleHomElementFamilyMap A D q h ≫ homRelationsLeft A D M N =
      moduleHomElementFamilyMap A D q h ≫ homRelationsRight A D M N := by
  apply Pi.hom_ext
  rintro ⟨x, y⟩
  simp only [homRelationsLeft, homRelationsRight, Category.assoc, homRelations, Pi.lift_comp_π]
  rw [← curryRight_naturality_source, ← curryRight_naturality_source,
    homNaturalityLeft_precomp, homNaturalityRight_precomp]
  simp only [moduleHomElementFamilyMap, Pi.lift_comp_π]
  exact moduleHomDiskFamily_naturality A q h hn (op x) (op y)

def moduleHomElementMk {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q)
    (hn : ∀ (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p),
      ((M.map x y).f p f).comp (h y) (by omega : p + q = q + p) =
        (q * p).negOnePow • ((h x).comp ((N.map x y).f p f) rfl)) :
    (moduleHom A D M N).X q :=
  complexDiskHomEquiv A _ q
    (equalizer.lift (moduleHomElementFamilyMap A D q h)
      (moduleHomElementFamilyMap_condition A D q h hn))

lemma moduleHomElementMk_π {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q) (hn) (x : D) :
    (moduleHomπ A D M N x).f q (moduleHomElementMk A D q h hn) = h (op x) := by
  have hp : equalizer.lift (moduleHomElementFamilyMap A D q h)
      (moduleHomElementFamilyMap_condition A D q h hn) ≫ moduleHomπ A D M N x =
    (complexDiskHomEquiv A (homComplex A (M.obj (op x)) (N.obj (op x))) q).symm (h (op x)) := by
    simp only [moduleHomπ, equalizer.lift_ι_assoc, moduleHomElementFamilyMap, Pi.lift_comp_π]
  have he := congrArg (complexDiskHomEquiv A _ q) hp
  rw [complexDiskHomEquiv_naturality, Equiv.apply_symm_apply] at he
  exact he

lemma moduleHomElement_ext {M N : RightModule A D} {q : ℤ}
    {z w : (moduleHom A D M N).X q}
    (h : ∀ x : D, (moduleHomπ A D M N x).f q z = (moduleHomπ A D M N x).f q w) : z = w := by
  apply (complexDiskHomEquiv A (moduleHom A D M N) q).symm.injective
  apply moduleHom_ext
  intro x
  apply (complexDiskHomEquiv A _ q).injective
  rw [complexDiskHomEquiv_naturality, complexDiskHomEquiv_naturality,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h x

/-- 主Hom endの任意の斉次要素の全次数自然性。 -/
lemma moduleHomElement_naturality {M N : RightModule A D} (q : ℤ)
    (z : (moduleHom A D M N).X q) (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p) :
    ((M.map x y).f p f).comp ((moduleHomπ A D M N y.unop).f q z)
        (by omega : p + q = q + p) =
      (q * p).negOnePow • (((moduleHomπ A D M N x.unop).f q z).comp
        ((N.map x y).f p f) rfl) := by
  let σ := fun t : Dᵒᵖ => moduleHomπ A D M N t.unop
  have hL := moduleParamRelationLeft_apply A (M := M) (N := N) σ x y q p z f
  have hR := moduleParamRelationRight_apply A (M := M) (N := N) σ x y q p z f
  have hc := congrArg (fun a => (a.f q z).v p (q + p) (by omega) f)
    (congrArg curryRight (moduleHomπ_naturality A D M N x y))
  exact hL.symm.trans (hc.trans hR)

/-- 成分を取り出して再構成すると元の斉次要素を得る。 -/
lemma moduleHomElementMk_components {M N : RightModule A D} (q : ℤ)
    (z : (moduleHom A D M N).X q) :
    moduleHomElementMk A D q (fun x => (moduleHomπ A D M N x.unop).f q z)
      (moduleHomElement_naturality A D q z) = z := by
  apply moduleHomElement_ext A D
  intro x
  exact moduleHomElementMk_π A D q _ _ x

lemma moduleHomElement_d_π {M N : RightModule A D} (q r : ℤ)
    (z : (moduleHom A D M N).X q) (x : D) :
    (moduleHomπ A D M N x).f r ((moduleHom A D M N).d q r z) =
      δ q r ((moduleHomπ A D M N x).f q z) := by
  have h := congrArg (fun a => a z) ((moduleHomπ A D M N x).comm q r)
  exact h.symm

end SerrePositivity.DifferentialGraded
