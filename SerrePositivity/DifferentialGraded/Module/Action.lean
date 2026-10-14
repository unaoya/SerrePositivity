module
public import SerrePositivity.DifferentialGraded.Module.Representable
public import SerrePositivity.DifferentialGraded.Module.Hom

/-! # 右 dg 加群の斉次作用と全次数自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 豊穣 Hom 射を評価する右加群の斉次作用。 -/
def moduleAction (M : RightModule A D) {x y : Dᵒᵖ} {p q n : ℤ}
    (f : GradedHom A x y p) (v : (M.obj x).X q) (hn : q + p = n) : (M.obj y).X n :=
  ((M.map x y).f p f).v q n hn v

/-- 右作用の単位則。 -/
lemma moduleAction_unit (M : RightModule A D) (x : Dᵒᵖ) (q : ℤ) (v : (M.obj x).X q) :
    moduleAction A M (unitElement A x).val v (add_zero q) = v := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (M.toFunctor.map_id x)
  rw [cycleFromUnit_postcomp] at h
  change (M.map x x).f 0 (unitElement A x).val =
    (cycleFromUnit _ (identity (M.obj x))).val at h
  rw [identity, cycleFromUnit_unitFromCycle] at h
  unfold moduleAction
  rw [h]
  rfl

/-- 作用は豊穣順の合成に対して Koszul 符号付きで結合する。 -/
lemma moduleAction_forward (M : RightModule A D) {x y z : Dᵒᵖ} {p q r m n s : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (v : (M.obj x).X r)
    (hm : p + q = m) (hs : r + p = s) (hn : r + m = n) :
    moduleAction A M (forward A f g hm) v hn = (p * q).negOnePow •
      moduleAction A M g (moduleAction A M f v hs) (by omega) := by
  have h := M.toFunctor.map_comp x y z
  have hh := congrArg (fun l => l.f m
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q m hm (f ⊗ₜ[A] g))) h
  change (M.map x z).f m (forward A f g hm) = _ at hh
  change (M.map x z).f m (forward A f g hm) =
    (enrichedComposition _ _ _).f m
      (((M.map x y) ⊗ₘ (M.map y z)).f m
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q m hm (f ⊗ₜ[A] g))) at hh
  rw [tensorMap_apply, enrichedComposition_apply] at hh
  unfold moduleAction
  rw [hh, Cochain.units_smul_v, Cochain.comp_v _ _ hm r s n hs (by omega)]
  rfl

/-- 全次数自然性の成分公式。通常の閉零射だけに課す条件より強い。 -/
lemma moduleParamNaturality_apply {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (h : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _ =
        (σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _)
    {x y : Dᵒᵖ} {k p r m n : ℤ}
    (t : K.X k) (f : GradedHom A x y p) (v : (M.obj x).X r)
    (hm : k + p = m) (hn : r + m = n) :
    ((σ y).f k t).v (r + p) n (by omega) (moduleAction A M f v rfl) =
      (k * p).negOnePow • moduleAction A N f
        (((σ x).f k t).v r (r + k) rfl v) (by omega) := by
  have hh := congrArg (fun l => l.f m
    (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f))) (h x y)
  change (enrichedComposition _ _ _).f m
    (((M.map x y) ⊗ₘ (σ y)).f m
      ((signedSwap K (x ⟶[Complex A] y)).hom.f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f)))) =
    (enrichedComposition _ _ _).f m
      (((σ x) ⊗ₘ (N.map x y)).f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f))) at hh
  rw [signedSwap_apply] at hh
  simp only [Units.smul_def, map_zsmul] at hh
  change (k * p).negOnePow • (enrichedComposition _ _ _).f m
      (((M.map x y) ⊗ₘ (σ y)).f m
        (ιTensorObj (x ⟶[Complex A] y) K p k m (by omega) (f ⊗ₜ[A] t))) = _ at hh
  simp only [tensorMap_apply, enrichedComposition_apply] at hh
  rw [mul_comm p k, smul_smul, Int.units_mul_self, one_smul] at hh
  have hv := congrArg (fun c => c.v r n hn v) hh
  rw [Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega) r (r + p) n rfl (by omega),
    Cochain.comp_v _ _ hm r (r + k) n rfl (by omega)] at hv
  exact hv
/-- 中間次数を指定して自然性の成分公式を使う。 -/
lemma moduleParamNaturality_apply_of_sum {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (h : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _ =
        (σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _)
    {x y : Dᵒᵖ} {k p r m n s l : ℤ}
    (t : K.X k) (f : GradedHom A x y p) (v : (M.obj x).X r)
    (hm : k + p = m) (hn : r + m = n) (hs : r + p = s) (hl : r + k = l) :
    ((σ y).f k t).v s n (by omega) (moduleAction A M f v hs) =
      (k * p).negOnePow • moduleAction A N f
        (((σ x).f k t).v r l hl v) (by omega) := by
  subst s l
  exact moduleParamNaturality_apply A σ h t f v hm hn

/-- 全斉次成分の符号付き作用公式から全豊穣自然性を復元する。 -/
lemma moduleParamNaturality_of_apply {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (h : ∀ (x y : Dᵒᵖ) (k p r n : ℤ) (hn : r + (k + p) = n)
      (t : K.X k) (f : GradedHom A x y p) (v : (M.obj x).X r),
      ((σ y).f k t).v (r + p) n (by omega) (moduleAction A M f v rfl) =
        (k * p).negOnePow • moduleAction A N f
          (((σ x).f k t).v r (r + k) rfl v) (by omega)) (x y : Dᵒᵖ) :
    (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _ =
        (σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _ := by
  apply tensorHom_ext
  intro k p m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t f
  change (enrichedComposition _ _ _).f m
    (((M.map x y) ⊗ₘ σ y).f m
      ((signedSwap K (x ⟶[Complex A] y)).hom.f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f)))) =
    (enrichedComposition _ _ _).f m
      (((σ x) ⊗ₘ N.map x y).f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f)))
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (k * p).negOnePow • (enrichedComposition _ _ _).f m
      (((M.map x y) ⊗ₘ σ y).f m
        (ιTensorObj (x ⟶[Complex A] y) K p k m (by omega) (f ⊗ₜ[A] t))) = _
  rw [tensorMap_apply, tensorMap_apply, enrichedComposition_apply,
    enrichedComposition_apply, mul_comm p k, smul_smul,
    Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega) r (r + p) n rfl (by omega),
    Cochain.comp_v _ _ hm r (r + k) n rfl (by omega)]
  exact h x y k p r n (by omega) t f v

/-- Mathlib パラメータ付き自然変換の符号付き作用公式。 -/
lemma moduleParamTrans_apply {K : Complex A} {M N : RightModule A D}
    (τ : ModuleParamTrans A D K M N) {x y : Dᵒᵖ} {k p r m n : ℤ}
    (t : K.X k) (f : GradedHom A x y p) (v : (M.obj x).X r)
    (hm : k + p = m) (hn : r + m = n) :
    ((τ.app y).f k t).v (r + p) n (by omega) (moduleAction A M f v rfl) =
      (k * p).negOnePow • moduleAction A N f
        (((τ.app x).f k t).v r (r + k) rfl v) (by omega) :=
  moduleParamNaturality_apply A τ.app τ.naturality t f v hm hn
end SerrePositivity.DifferentialGraded
