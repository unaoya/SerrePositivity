module
public import SerrePositivity.DifferentialGraded.Category.Examples
public import SerrePositivity.DifferentialGraded.Complexes.Closed

/-! # 通常 chain map の閉零豊穣射と Hom 関手性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 通常 chain map を単位複体からの閉零豊穣射として読む。 -/
abbrev closedMap {P Q : Complex A} (f : P ⟶ Q) :
    𝟙_ (Complex A) ⟶ homComplex A P Q := (complexClosedHomEquiv A P Q).symm f

/-- 閉零豊穣射の cycle は元の chain map の次数零 cochain。 -/
lemma closedMap_cycle {P Q : Complex A} (f : P ⟶ Q) :
    (cycleFromUnit _ (closedMap A f)).val = Cochain.ofHom f := by
  have h := complexClosedHomEquiv_cochain A P Q ((complexClosedHomEquiv A P Q).symm f)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Hom の後合成は閉零射との豊穣合成。 -/
lemma homPostcompose_closedMap (P : Complex A) {Q T : Complex A} (f : Q ⟶ T) :
    homPostcompose P f = (ρ_ (homComplex A P Q)).inv ≫
      homComplex A P Q ◁ closedMap A f ≫ enrichedComposition P Q T := by
  apply HomologicalComplex.Hom.ext
  funext p
  change (homPostcompose P f).f p = (rightUnitor' (homComplex A P Q)).inv p ≫
    (homComplex A P Q ◁ closedMap A f).f p ≫ (enrichedComposition P Q T).f p
  rw [rightUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerLeft_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change h.comp (Cochain.ofHom f) (add_zero p) = (enrichedComposition P Q T).f p
    (ιTensorObj (homComplex A P Q) (homComplex A Q T) p 0 p (add_zero p)
      (h ⊗ₜ[A] (cycleFromUnit _ (closedMap A f)).val))
  rw [enrichedComposition_apply, closedMap_cycle]
  simp

/-- Hom の前合成は閉零射との豊穣合成。 -/
lemma homPrecompose_closedMap {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    homPrecompose f T = (λ_ (homComplex A Q T)).inv ≫
      closedMap A f ▷ homComplex A Q T ≫ enrichedComposition P Q T := by
  apply HomologicalComplex.Hom.ext
  funext p
  change (homPrecompose f T).f p = (leftUnitor' (homComplex A Q T)).inv p ≫
    (closedMap A f ▷ homComplex A Q T).f p ≫ (enrichedComposition P Q T).f p
  rw [leftUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerRight_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change (Cochain.ofHom f).comp h (zero_add p) = (enrichedComposition P Q T).f p
    (ιTensorObj (homComplex A P Q) (homComplex A Q T) 0 p p (zero_add p)
      ((cycleFromUnit _ (closedMap A f)).val ⊗ₜ[A] h))
  rw [enrichedComposition_apply, closedMap_cycle]
  simp
/-- 単位からの閉射を通常の chain map として読む。 -/
abbrev mapFromUnit (P Q : Complex A) (f : 𝟙_ (Complex A) ⟶ homComplex A P Q) : P ⟶ Q :=
  complexClosedHomEquiv A P Q (ForgetEnrichment.homOf (Complex A) (C := Complex A)
    (X := P) (Y := Q) f)

/-- 通常射の閉射への変換は往復して戻る。 -/
@[simp]
lemma mapFromUnit_closedMap {P Q : Complex A} (f : P ⟶ Q) :
    mapFromUnit A P Q (closedMap A (P := P) (Q := Q) f) = f :=
  Equiv.apply_symm_apply (complexClosedHomEquiv A P Q) f

/-- 閉射の通常射への変換も往復して戻る。 -/
@[simp]
lemma closedMap_mapFromUnit (P Q : Complex A) (f : 𝟙_ (Complex A) ⟶ homComplex A P Q) :
    closedMap A (P := P) (Q := Q) (mapFromUnit A P Q f) = f :=
  Equiv.symm_apply_apply (complexClosedHomEquiv A P Q) _

/-- 閉射を通常射にしたときの零次数 cochain。 -/
lemma mapFromUnit_cochain (P Q : Complex A) (f : 𝟙_ (Complex A) ⟶ homComplex A P Q) :
    Cochain.ofHom (mapFromUnit A P Q f) = (cycleFromUnit _ f).val :=
  complexClosedHomEquiv_cochain A P Q _
/-- Mathlib の豊穣 Hom 後合成と明示線形 Hom 後合成は一致する。 -/
lemma complexHomWhiskerLeft (P : Complex A) {Q T : Complex A} (f : Q ⟶ T) :
    eHomWhiskerLeft (Complex A) P f = homPostcompose P f :=
  (homPostcompose_closedMap A P f).symm

/-- Mathlib の豊穣 Hom 前合成と明示線形 Hom 前合成は一致する。 -/
lemma complexHomWhiskerRight {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    eHomWhiskerRight (Complex A) f T = homPrecompose f T :=
  (homPrecompose_closedMap A f T).symm

/-- 明示した Hom 前合成の合成則。 -/
@[reassoc]
lemma homPrecompose_comp {P Q R : Complex A} (f : P ⟶ Q) (g : Q ⟶ R) (T : Complex A) :
    homPrecompose (f ≫ g) T = homPrecompose g T ≫ homPrecompose f T := by
  rw [← complexHomWhiskerRight, ← complexHomWhiskerRight, ← complexHomWhiskerRight,
    eHomWhiskerRight_comp]

/-- 明示した Hom 前合成・後合成は可換。 -/
@[reassoc]
lemma homPostcompose_precompose {P Q R T : Complex A} (f : P ⟶ Q) (g : R ⟶ T) :
    homPostcompose Q g ≫ homPrecompose f T = homPrecompose f R ≫ homPostcompose P g := by
  rw [← complexHomWhiskerLeft, ← complexHomWhiskerLeft,
    ← complexHomWhiskerRight, ← complexHomWhiskerRight]
  exact eHom_whisker_exchange (Complex A) f g
end SerrePositivity.DifferentialGraded
