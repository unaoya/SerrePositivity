module
public import SerrePositivity.DifferentialGraded.Tensor.LeftYoneda
public import SerrePositivity.DifferentialGraded.Module.LeftHomElements

/-! # balanced tensorのYoneda評価の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

@[reassoc]
lemma yonedaEvaluation_naturality (z : D) {N N' : LeftModuleCategory A D} (g : N ⟶ N') :
    map A D (𝟙 (ForgetEnrichment.of (Complex A) (representable A z))) g ≫
      yonedaEvaluation A D z (ForgetEnrichment.to (Complex A) N') =
    yonedaEvaluation A D z (ForgetEnrichment.to (Complex A) N) ≫
      (leftModuleEvaluation A D z).map g := by
  apply hom_ext
  intro x
  simp only [ι_map_assoc, CategoryTheory.Functor.map_id]
  change (𝟙 (x ⟶[Complex A] z) ⊗ₘ (leftModuleEvaluation A D x).map g) ≫
      ι A D (representable A z) (ForgetEnrichment.to (Complex A) N') x ≫
        yonedaEvaluation A D z (ForgetEnrichment.to (Complex A) N') =
    ι A D (representable A z) (ForgetEnrichment.to (Complex A) N) x ≫
      yonedaEvaluation A D z (ForgetEnrichment.to (Complex A) N) ≫
        (leftModuleEvaluation A D z).map g
  rw [ι_yonedaEvaluation, ι_yonedaEvaluation_assoc]
  exact (leftAction_morphism A D g x z).symm

@[reassoc]
lemma leftYonedaEvaluation_naturality (z : D) {M M' : ModuleCategory A D} (f : M ⟶ M') :
    map A D f (𝟙 (ForgetEnrichment.of (Complex A) (leftRepresentable A z))) ≫
      leftYonedaEvaluation A D z (ForgetEnrichment.to (Complex A) M') =
    leftYonedaEvaluation A D z (ForgetEnrichment.to (Complex A) M) ≫
      (moduleEvaluation A D z).map f := by
  apply hom_ext
  intro x
  simp only [ι_map_assoc, CategoryTheory.Functor.map_id]
  change ((moduleEvaluation A D x).map f ⊗ₘ 𝟙 (z ⟶[Complex A] x)) ≫
      ι A D (ForgetEnrichment.to (Complex A) M') (leftRepresentable A z) x ≫
        leftYonedaEvaluation A D z (ForgetEnrichment.to (Complex A) M') =
    ι A D (ForgetEnrichment.to (Complex A) M) (leftRepresentable A z) x ≫
      leftYonedaEvaluation A D z (ForgetEnrichment.to (Complex A) M) ≫
        (moduleEvaluation A D z).map f
  rw [ι_leftYonedaEvaluation, ι_leftYonedaEvaluation_assoc]
  exact (rightAction_morphism A D f z x).symm

/-- 左加群の任意次数のHomに対するYoneda評価の生成元上の自然性。 -/
lemma yonedaEvaluation_homElement {N N' : LeftModule A D} {q p r n k l : ℤ}
    (τ : (leftModuleHom A D N N').X q) (z x : D)
    (f : GradedHom A x z p) (m : (N.obj x).X r)
    (hn : p + r = n) (hk : r + q = k) (hl : n + q = l) :
    (((leftModuleHomπ A D N N' z).f q τ).v n l hl)
      ((yonedaEvaluation A D z N).f n (element A D (representable A z) N x f m hn)) =
    (q * p).negOnePow • (yonedaEvaluation A D z N').f l
      (element A D (representable A z) N' x f
        ((((leftModuleHomπ A D N N' x).f q τ).v r k hk) m) (by omega)) := by
  rw [yonedaEvaluation_element, yonedaEvaluation_element]
  exact leftModuleHomElement_action A D τ x z f m (by omega) hk hl

/-- 右加群の任意次数のHomに対する反対側の評価の生成元上の自然性。 -/
lemma leftYonedaEvaluation_homElement {M M' : RightModule A D} {q p r n k l : ℤ}
    (τ : (moduleHom A D M M').X q) (z x : D)
    (m : (M.obj (op x)).X r) (f : GradedHom A z x p)
    (hn : r + p = n) (hk : r + q = k) (hl : n + q = l) :
    (((moduleHomπ A D M M' z).f q τ).v n l hl)
      ((leftYonedaEvaluation A D z M).f n
        (element A D M (leftRepresentable A z) x m f hn)) =
    (leftYonedaEvaluation A D z M').f l
      (element A D M' (leftRepresentable A z) x
        ((((moduleHomπ A D M M' x).f q τ).v r k hk) m) f (by omega)) := by
  have h := Cochain.congr_v (moduleHomElement_naturality A D q τ (op x) (op z) p f)
    r l (by omega)
  rw [Cochain.comp_v _ _ _ r n l hn hl, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ r k l hk (by omega)] at h
  have he := congrArg (fun t => t m) h
  change (((moduleHomπ A D M M' z).f q τ).v n l hl) (moduleAction A M f m hn) =
    (q * p).negOnePow • moduleAction A M' f
      ((((moduleHomπ A D M M' x).f q τ).v r k hk) m) (by omega) at he
  rw [leftYonedaEvaluation_element, leftYonedaEvaluation_element]
  simp only [Units.smul_def, map_zsmul]
  change (r * p).negOnePow •
    ((((moduleHomπ A D M M' z).f q τ).v n l hl) (moduleAction A M f m hn)) =
    (k * p).negOnePow • moduleAction A M' f
      ((((moduleHomπ A D M M' x).f q τ).v r k hk) m) (by omega)
  rw [he]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : r * p + q * p = k * p := by
    rw [← hk]
    ring
  rw [hs]

end SerrePositivity.DifferentialGraded.BalancedTensor
