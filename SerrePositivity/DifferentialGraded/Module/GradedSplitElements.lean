module
public import SerrePositivity.DifferentialGraded.Module.HomElementComposition
public import SerrePositivity.DifferentialGraded.Module.GradedSplit

/-! # 次数付き自然変換と分裂の主Hom end要素

微分との可換性を要求しない次数零要素としてretractionとsectionを扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleGradedNaturalElement {M N : ModuleCategory A D}
    (a : ∀ x : D, ∀ n : ℤ,
      ((moduleEvaluation A D x).obj M).X n ⟶ ((moduleEvaluation A D x).obj N).X n)
    (ha : ∀ (x y : D) (p i j : ℤ) (hij : i + p = j)
      (f : GradedHom A (op x) (op y) p),
      moduleActionComponent A D M x y p i j hij f ≫ a y j =
        a x i ≫ moduleActionComponent A D N x y p i j hij f) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).X 0 :=
  moduleHomElementMk A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) N) 0 (fun x => Cochain.ofHoms (a x.unop)) (by
    intro x y p f
    simp only [zero_mul, Int.negOnePow_zero, one_smul]
    apply Cochain.ext
    intro i j hij
    rw [Cochain.comp_v _ _ _ i j j (by omega) (add_zero j),
      Cochain.comp_v _ _ _ i i j (add_zero i) (by omega)]
    simp only [Cochain.ofHoms_v]
    exact ha x.unop y.unop p i j (by omega) f)

lemma moduleGradedNaturalElement_π {M N : ModuleCategory A D} (a) (ha) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) x).f 0 (moduleGradedNaturalElement A D a ha) =
        Cochain.ofHoms (a x) := moduleHomElementMk_π A D 0 _ _ x

namespace ModuleGradedSplit
variable {A D} {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

def retractionElement (s : ModuleGradedSplit A D f g) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) M)).X 0 :=
  moduleGradedNaturalElement A D s.retraction s.retraction_naturality

def sectionElement (s : ModuleGradedSplit A D f g) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N)).X 0 :=
  moduleGradedNaturalElement A D s.section_
    (fun x y p i j hij a => (s.section_naturality x y p i j hij a).symm)

lemma retractionElement_π (s : ModuleGradedSplit A D f g) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) M) x).f 0 s.retractionElement =
        Cochain.ofHoms (s.retraction x) := moduleGradedNaturalElement_π A D _ _ x

lemma sectionElement_π (s : ModuleGradedSplit A D f g) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N) x).f 0 s.sectionElement =
        Cochain.ofHoms (s.section_ x) := moduleGradedNaturalElement_π A D _ _ x

/-- 包含への前合成を次数ごとに分裂する。chain mapとは主張しない。 -/
def homRestrictionSection (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q :=
  forward A (x := ForgetEnrichment.to (Complex A) N)
    (y := ForgetEnrichment.to (Complex A) M) (z := ForgetEnrichment.to (Complex A) T)
    s.retractionElement z (zero_add q)

lemma homRestrictionSection_π (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T) x).f q (s.homRestrictionSection T q z) =
      (Cochain.ofHoms (s.retraction x)).comp
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) T) x).f q z) (zero_add q) := by
  rw [homRestrictionSection, moduleHomForward_π, zero_mul, Int.negOnePow_zero,
    one_smul, s.retractionElement_π]

lemma homRestriction_section (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (eHomWhiskerRight (Complex A) f T).f q (s.homRestrictionSection T q z) = z := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomWhiskerRight_apply_π A D f q _ x, s.homRestrictionSection_π]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHoms_v]
  rw [← Category.assoc, s.inclusion_retraction, Category.id_comp]

lemma homRestriction_surjective (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) : Function.Surjective ((eHomWhiskerRight (Complex A) f T).f q) :=
  fun z => ⟨s.homRestrictionSection T q z, s.homRestriction_section T q z⟩

end ModuleGradedSplit
end SerrePositivity.DifferentialGraded
