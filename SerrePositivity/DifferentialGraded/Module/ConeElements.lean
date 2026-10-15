module
public import SerrePositivity.DifferentialGraded.Module.GradedSplitElements
public import SerrePositivity.DifferentialGraded.Module.HomFunctor
public import SerrePositivity.DifferentialGraded.Module.ConeGradedSplit

/-! # coneの包含・射影を主Hom endの斉次要素として構成

左包含は次数−1、第一射影は次数+1、第二射影は次数0である。
微分と全dg自然性をともに保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeInlElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X (-1) :=
  moduleHomElementMk A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1)
    (fun x => mappingCone.inl ((moduleEvaluation A D x.unop).map f)) (by
      intro x y p a
      apply Cochain.ext
      intro i j hij
      obtain ⟨k, rfl⟩ : ∃ k : ℤ, i = k + 1 := ⟨i - 1, by omega⟩
      rw [Cochain.units_smul_v,
        Cochain.comp_v _ _ _ (k + 1) (j + 1) j (by omega) (by omega),
        Cochain.comp_v _ _ _ (k + 1) k j (by omega) (by omega)]
      change _ = (-1 * p).negOnePow •
        ((mappingCone.inl ((moduleEvaluation A D x.unop).map f)).v (k + 1) k (by omega) ≫
          (coneMapCochain ((moduleEvaluation A D x.unop).map f)
            ((moduleEvaluation A D y.unop).map f)
            (((ForgetEnrichment.to (Complex A) M).map x y).f p a)
            (((ForgetEnrichment.to (Complex A) N).map x y).f p a)).v k j (by omega))
      rw [coneMapCochain_inl_v]
      simp only [neg_one_mul, Int.negOnePow_neg, smul_smul, Int.units_mul_self, one_smul])


lemma moduleConeInlElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f (-1)
        (moduleConeInlElement A D f) = mappingCone.inl ((moduleEvaluation A D x).map f) :=
  moduleHomElementMk_π A D (-1) _ _ x

def moduleConeFstElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) M)).X 1 :=
  moduleHomElementMk A D (M := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (N := ForgetEnrichment.to (Complex A) M) 1
    (fun x => (mappingCone.fst ((moduleEvaluation A D x.unop).map f)).val) (by
      intro x y p a
      apply Cochain.ext
      intro i j hij
      rw [Cochain.units_smul_v,
        Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
        Cochain.comp_v _ _ _ i (i + 1) j rfl (by omega)]
      have h := Cochain.congr_v (coneMapCochain_fst
        ((moduleEvaluation A D x.unop).map f) ((moduleEvaluation A D y.unop).map f)
        (((ForgetEnrichment.to (Complex A) M).map x y).f p a)
        (((ForgetEnrichment.to (Complex A) N).map x y).f p a)) i j (by omega)
      rw [Cochain.units_smul_v,
        Cochain.comp_v _ _ rfl i (i + p) j rfl (by omega),
        Cochain.comp_v _ _ (by omega : 1 + p = p + 1) i (i + 1) j rfl (by omega)] at h
      change (coneMapCochain ((moduleEvaluation A D x.unop).map f)
        ((moduleEvaluation A D y.unop).map f)
        (((ForgetEnrichment.to (Complex A) M).map x y).f p a)
        (((ForgetEnrichment.to (Complex A) N).map x y).f p a)).v i (i + p) rfl ≫
          (mappingCone.fst ((moduleEvaluation A D y.unop).map f)).val.v (i + p) j (by omega) = _
      simpa only [one_mul] using h)


lemma moduleConeFstElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) M) x).f 1 (moduleConeFstElement A D f) =
        (mappingCone.fst ((moduleEvaluation A D x).map f)).val :=
  moduleHomElementMk_π A D 1 _ _ x

def moduleConeSndElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) N)).X 0 :=
  (moduleConeGradedSplit A D f).retractionElement

lemma moduleConeSndElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) N) x).f 0 (moduleConeSndElement A D f) =
        mappingCone.snd ((moduleEvaluation A D x).map f) := by
  rw [moduleConeSndElement, ModuleGradedSplit.retractionElement_π]
  rfl

lemma moduleConeInlElement_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-1) 0
        (moduleConeInlElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (f ≫ moduleConeInr A D f))).val := by
  apply moduleHomElement_ext A D
    (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f))
  intro x
  rw [moduleHomElement_d_π, moduleConeInlElement_π, mappingCone.δ_inl,
    ← moduleEvaluation_cochain, CategoryTheory.Functor.map_comp, moduleConeInr_eval]

lemma moduleConeFstElement_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) M)).d 1 2 (moduleConeFstElement A D f) = 0 := by
  apply moduleHomElement_ext A D
    (M := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (N := ForgetEnrichment.to (Complex A) M)
  intro x
  rw [moduleHomElement_d_π, moduleConeFstElement_π, map_zero]
  exact Cocycle.δ_eq_zero _ _

end SerrePositivity.DifferentialGraded
