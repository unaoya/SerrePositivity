module
public import SerrePositivity.DifferentialGraded.Module.ConeElements
public import SerrePositivity.DifferentialGraded.Module.Postcomposition

/-! # 主Hom endと標準coneの比較射

左包含の微分公式を転置して、Mathlibのconeのdescを適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleHomConeLeftCochain (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    Homogeneous (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M))
      (moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f))) (-1) :=
  (modulePostcompositionMap A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f (-1)
      (moduleConeInlElement A D f)

lemma moduleHomConeLeftCochain_d (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) : δ (-1) 0 (moduleHomConeLeftCochain A D T f) =
      Cochain.ofHom (eHomWhiskerLeft (Complex A) T f ≫
        eHomWhiskerLeft (Complex A) T (moduleConeInr A D f)) := by
  rw [moduleHomConeLeftCochain, modulePostcompositionMap_d, moduleConeInlElement_d,
    modulePostcompositionMap_closed, eHomWhiskerLeft_comp]

lemma moduleHomConeLeftCochain_π (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q n : ℤ) (hn : q + (-1) = n)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f n
        ((moduleHomConeLeftCochain A D T f).v q n hn z) =
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) M) x).f q z).comp
          (mappingCone.inl ((moduleEvaluation A D x).map f)) hn := by
  rw [moduleHomConeLeftCochain, modulePostcompositionMap_apply, moduleHomCompose_π,
    moduleConeInlElement_π]

def moduleHomConeComparison (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    mappingCone (eHomWhiskerLeft (Complex A) T f) ⟶
      moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) :=
  mappingCone.desc (eHomWhiskerLeft (Complex A) T f) (moduleHomConeLeftCochain A D T f)
    (eHomWhiskerLeft (Complex A) T (moduleConeInr A D f))
    (moduleHomConeLeftCochain_d A D T f)

@[reassoc] lemma moduleHomConeComparison_inr (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone.inr (eHomWhiskerLeft (Complex A) T f) ≫ moduleHomConeComparison A D T f =
      eHomWhiskerLeft (Complex A) T (moduleConeInr A D f) :=
  mappingCone.inr_desc _ _ _ _

lemma moduleHomConeComparison_apply_π (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q : ℤ) (z : (mappingCone (eHomWhiskerLeft (Complex A) T f)).X q)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q
        ((moduleHomConeComparison A D T f).f q z) =
      mappingCone.liftCochain ((moduleEvaluation A D x).map f)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) M) x).f (q + 1)
            ((mappingCone.fst (eHomWhiskerLeft (Complex A) T f)).val.v q (q + 1) rfl z))
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N) x).f q
            ((mappingCone.snd (eHomWhiskerLeft (Complex A) T f)).v q q (add_zero q) z)) rfl := by
  rw [moduleHomConeComparison,
    mappingCone.desc_f _ _ _ _ q (q + 1) rfl]
  change (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q
      ((moduleHomConeLeftCochain A D T f).v (q + 1) q (by omega)
        ((mappingCone.fst (eHomWhiskerLeft (Complex A) T f)).val.v q (q + 1) rfl z) +
       (show (moduleHom A D (ForgetEnrichment.to (Complex A) T)
         (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q from
         (eHomWhiskerLeft (Complex A) T (moduleConeInr A D f)).f q
           ((mappingCone.snd (eHomWhiskerLeft (Complex A) T f)).v q q (add_zero q) z))) = _
  rw [map_add, moduleHomConeLeftCochain_π, moduleHomWhiskerLeft_apply_π, moduleConeInr_eval]
  rfl

end SerrePositivity.DifferentialGraded
