module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonHomPresheaf
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiniteRoof
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction

/-! # 商内の代表対象への射と制限代表加群への導来 Hom -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定 Verdier 商の射を、代表加群比較の像に作用させる。 -/
def quotientRepresentableHomMap (S : Set D) (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    (triaInclusion A D).obj X ⟶ (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z)) :=
  quotientRestrictionLocalizedHomEquiv A D S z X
    ((quotientRestrictionLocalizedHom A D S z).map f.op
      ((quotientRestrictionLocalizedHomEquiv A D S z (triaRepresentable A D z)).symm
        ((moduleToDerived A D).map
          (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))))

lemma quotientRepresentableHomMap_map (S : Set D) (z : D) {X : TriaCategory A D}
    (f : X ⟶ triaRepresentable A D z) :
    quotientRepresentableHomMap A D S z X ((triaQuotient A D S).map f) =
      (triaInclusion A D).map f ≫ (moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) := by
  unfold quotientRepresentableHomMap
  rw [quotientRestrictionLocalizedHomEquiv_naturality, Equiv.apply_symm_apply]

lemma quotientRepresentableHomMap_precomp (S : Set D) (z : D)
    {X Y : TriaCategory A D} (s : X ⟶ Y)
    (f : (triaQuotient A D S).obj Y ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    quotientRepresentableHomMap A D S z X ((triaQuotient A D S).map s ≫ f) =
      (triaInclusion A D).map s ≫ quotientRepresentableHomMap A D S z Y f := by
  unfold quotientRepresentableHomMap
  rw [op_comp, CategoryTheory.Functor.map_comp]
  exact quotientRestrictionLocalizedHomEquiv_naturality A D S z s _

/-- 局所 K-flat 仮定の下で、この Hom 比較は全射。 -/
lemma quotientRepresentableHomMap_surjective (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D) :
    Function.Surjective (quotientRepresentableHomMap A D S z X) := by
  intro f
  obtain ⟨E, s, g, hs, hg⟩ := quotientRepresentable_exists_triaRoof A D S h z X f
  have : IsIso ((triaQuotient A D S).map s) :=
    Localization.inverts (triaQuotient A D S) (triaImage A D S).trW s hs
  let φ := inv ((triaQuotient A D S).map s) ≫ (triaQuotient A D S).map g
  refine ⟨φ, ?_⟩
  apply (quotientRepresentableRestriction_tria_precomp_bijective A D S z s hs).1
  dsimp only
  rw [← quotientRepresentableHomMap_precomp]
  have he : (triaQuotient A D S).map s ≫ φ = (triaQuotient A D S).map g := by
    simp [φ]
  rw [he, quotientRepresentableHomMap_map]
  exact hg

/-- 比較の値が零なら、Verdier 商の射そのものが零。 -/
lemma quotientRepresentableHomMap_eq_zero (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z))
    (hf : quotientRepresentableHomMap A D S z X f = 0) : f = 0 := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction
    (triaQuotient A D S) (triaImage A D S).trW f
  have he : (triaQuotient A D S).map φ.s ≫ f = (triaQuotient A D S).map φ.f := by
    rw [hφ, MorphismProperty.RightFraction.map_s_comp_map]
  have hz : (triaInclusion A D).map φ.f ≫ (moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) = 0 := by
    rw [← quotientRepresentableHomMap_map, ← he, quotientRepresentableHomMap_precomp,
      hf, comp_zero]
  have hg := triaQuotient_map_eq_zero_of_representableComparison A D S h z _ φ.f hz
  have : IsIso ((triaQuotient A D S).map φ.s) :=
    Localization.inverts (triaQuotient A D S) (triaImage A D S).trW φ.s φ.hs
  apply (cancel_epi ((triaQuotient A D S).map φ.s)).1
  rw [he, hg, comp_zero]

/-- 二つの分数を共通の分母に揃え、元の射の差の核を消すと単射性が得られる。 -/
lemma quotientRepresentableHomMap_injective (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D) :
    Function.Injective (quotientRepresentableHomMap A D S z X) := by
  intro f g hfg
  let Q := triaQuotient A D S
  let W := (triaImage A D S).trW
  obtain ⟨α, hα⟩ := Localization.exists_rightFraction Q W f
  obtain ⟨β, hβ⟩ := Localization.exists_rightFraction Q W g
  obtain ⟨γ, hγ⟩ := (MorphismProperty.LeftFraction.mk α.s β.s β.hs).exists_rightFraction
  let t := γ.s ≫ α.s
  let a := γ.s ≫ α.f
  let b := γ.f ≫ β.f
  have ht : W t := W.comp_mem _ _ γ.hs α.hs
  have ha : Q.map t ≫ f = Q.map a := by
    dsimp only [t, a]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      hα, MorphismProperty.RightFraction.map_s_comp_map]
  have hb : Q.map t ≫ g = Q.map b := by
    dsimp only [t, b]
    rw [hγ, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, hβ, MorphismProperty.RightFraction.map_s_comp_map]
  have he : (triaInclusion A D).map a ≫ (moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) =
      (triaInclusion A D).map b ≫ (moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) := by
    rw [← quotientRepresentableHomMap_map, ← quotientRepresentableHomMap_map, ← ha, ← hb,
      quotientRepresentableHomMap_precomp, quotientRepresentableHomMap_precomp, hfg]
  have hz : (triaInclusion A D).map (a - b) ≫ (moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) = 0 := by
    rw [Functor.map_sub, Preadditive.sub_comp, he, sub_self]
  have hab : Q.map a = Q.map b := by
    have hh := triaQuotient_map_eq_zero_of_representableComparison A D S h z _ (a - b) hz
    rw [Functor.map_sub, sub_eq_zero] at hh
    exact hh
  have : IsIso (Q.map t) := Localization.inverts Q W t ht
  apply (cancel_epi (Q.map t)).1
  exact ha.trans (hab.trans hb.symm)

/-- 局所 K-flat 版の代表対象を終域とする、指定 Verdier 商の実際の Hom 同値。 -/
def quotientRepresentableHomEquiv (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D) :
    ((triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) ≃
    ((triaInclusion A D).obj X ⟶ (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) :=
  Equiv.ofBijective (quotientRepresentableHomMap A D S z X)
    ⟨quotientRepresentableHomMap_injective A D S h z X,
      quotientRepresentableHomMap_surjective A D S h z X⟩

/-- 随伴によって、右辺を明示的 dg 商側の実際の導来 Hom に直す。 -/
def quotientDerivedRepresentableHomEquiv (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D) :
    ((triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) ≃
    ((dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).obj
        ((triaInclusion A D).obj X) ⟶
      (moduleToDerived A (QuotientObject D S)).obj
        (ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S)))) :=
  (quotientRepresentableHomEquiv A D S h z X).trans
    ((Iso.homCongr (Iso.refl _) (dgDerivedRestrictionComputation A D (QuotientObject D S)
      (inclusion A D S) (ForgetEnrichment.of (Complex A)
        (representable A (⟨z⟩ : QuotientObject D S)))).symm).trans
      (dgDerivedExtensionHomEquiv A D (QuotientObject D S) (inclusion A D S)
        ((triaInclusion A D).obj X) _).symm)

end SerrePositivity.DifferentialGraded.DGQuotient
