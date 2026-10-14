module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Complexes.CompositionLaws
public import SerrePositivity.DifferentialGraded.Complexes.UnitTensor
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # Ch(A) と一対象 A の dg 圏 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 非有界 A 複体の dg 圏。Hom は既存 linearHomComplex。
通常の chain map の Category instance は変更しない。 -/
instance complexEnrichment : DGCategory A (Complex A) where
  Hom := homComplex A
  id := identity
  comp := enrichedComposition
  id_comp := identity_comp
  comp_id := comp_identity
  assoc W X Y Z := by
    rw [enrichedComposition_assoc,
      Iso.inv_hom_id_assoc]

/-- 環 A の一対象 dg 圏。Hom は次数零の tensor unit A。 -/
instance ringEnrichment : DGCategory A PUnit where
  Hom _ _ := 𝟙_ (Complex A)
  id _ := 𝟙 _
  comp _ _ _ := (λ_ (𝟙_ (Complex A))).hom
  id_comp _ _ := by simp
  comp_id _ _ := by
    simp only [whiskerLeft_id]
    monoidal_coherence
  assoc _ _ _ _ := by monoidal_coherence

/-- Ch(A) の閉次数零射は通常の chain map に一致する。 -/
def complexClosedHomEquiv (X Y : Complex A) :
    (ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) ≃ (X ⟶ Y) :=
  (unitCycleEquiv (homComplex A X Y)).trans
    { toFun c := Cocycle.homOf ⟨c.val, c.property⟩
      invFun f := ⟨Cochain.ofHom f, δ_ofHom f⟩
      left_inv c := by
        apply Subtype.ext
        exact Cocycle.cochain_ofHom_homOf_eq_coe ⟨c.val, c.property⟩
      right_inv f := Cocycle.homOf_ofHom_eq_self f }
/-- 閉射の chain map への比較は、その次数零 cycle を返す。 -/
lemma complexClosedHomEquiv_cochain (X Y : Complex A)
    (f : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) :
    Cochain.ofHom (complexClosedHomEquiv A X Y f) =
      (cycleFromUnit (homComplex A X Y) f).val :=
  Cocycle.cochain_ofHom_homOf_eq_coe _

/-- Z⁰(Ch(A)) の単位は通常の恒等 chain map に一致する。 -/
lemma complexClosedHomEquiv_id (X : Complex A) :
    complexClosedHomEquiv A X X (𝟙 (ForgetEnrichment.of (Complex A) X)) = 𝟙 X := by
  apply Cochain.ofHom_injective
  rw [complexClosedHomEquiv_cochain]
  change (cycleFromUnit (homComplex A X X) (identity X)).val = _
  rw [identity, cycleFromUnit_unitFromCycle]

/-- Z⁰(Ch(A)) の合成は通常の chain map 合成に一致する。 -/
lemma complexClosedHomEquiv_comp (X Y Z : Complex A)
    (f : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y)
    (g : ForgetEnrichment.of (Complex A) Y ⟶ ForgetEnrichment.of (Complex A) Z) :
    complexClosedHomEquiv A X Z (f ≫ g) =
      complexClosedHomEquiv A X Y f ≫ complexClosedHomEquiv A Y Z g := by
  apply Cochain.ofHom_injective
  rw [complexClosedHomEquiv_cochain, Cochain.ofHom_comp,
    complexClosedHomEquiv_cochain, complexClosedHomEquiv_cochain]
  change (cycleFromUnit (homComplex A X Z)
    (((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)) ≫ enrichedComposition X Y Z)).val = _
  rw [cycleFromUnit_postcomp]
  change (enrichedComposition X Y Z).f 0
    ((((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)).f 0) (1 : A)) = _
  rw [unit_tensor_apply]
  change (enrichedComposition X Y Z).f 0
    (HomologicalComplex.ιTensorObj (homComplex A X Y) (homComplex A Y Z) 0 0 0 rfl
      ((cycleFromUnit (homComplex A X Y) f).val ⊗ₜ[A]
        (cycleFromUnit (homComplex A Y Z) g).val)) = _
  rw [enrichedComposition_apply]
  simp

/-- Z⁰(Ch(A)) から既存の非有界複体圏への比較関手。 -/
def closedToComplex : ClosedCategory A (Complex A) ⥤ Complex A where
  obj X := ForgetEnrichment.to (Complex A) X
  map f := complexClosedHomEquiv A _ _ f
  map_id X := complexClosedHomEquiv_id A X
  map_comp f g := complexClosedHomEquiv_comp A _ _ _ f g

/-- 比較関手は射に関して忠実。 -/
instance closedToComplexFaithful : (closedToComplex A).Faithful where
  map_injective := by
    intro X Y f g h
    exact (complexClosedHomEquiv A X Y).injective h

/-- 比較関手は射に関して充満。 -/
instance closedToComplexFull : (closedToComplex A).Full where
  map_surjective := (complexClosedHomEquiv A _ _).surjective
/-- 比較関手は対象に関して本質的全射。 -/
instance closedToComplexEssSurj : (closedToComplex A).EssSurj where
  mem_essImage Y := ⟨ForgetEnrichment.of (Complex A) Y, ⟨Iso.refl _⟩⟩

/-- 充満・忠実・本質的全射から比較関手の同値性を登録する。 -/
instance closedToComplexIsEquivalence : (closedToComplex A).IsEquivalence where

/-- 閉次数零圏と既存の非有界複体圏の同値。 -/
def complexClosedEquivalence : ClosedCategory A (Complex A) ≌ Complex A :=
  (closedToComplex A).asEquivalence

/-- 既存の複体の圏構造と dg 豊穣構造を Mathlib の標準クラスで接続する。 -/
instance complexEnrichedOrdinary : EnrichedOrdinaryCategory (Complex A) (Complex A) where
  homEquiv := (complexClosedHomEquiv A _ _).symm
  homEquiv_id X := by
    apply (complexClosedHomEquiv A X X).injective
    change (complexClosedHomEquiv A X X) ((complexClosedHomEquiv A X X).symm (𝟙 X)) =
      complexClosedHomEquiv A X X (𝟙 (ForgetEnrichment.of (Complex A) X))
    rw [Equiv.apply_symm_apply, complexClosedHomEquiv_id]
  homEquiv_comp {X Y Z} f g := by
    apply (complexClosedHomEquiv A X Z).injective
    change complexClosedHomEquiv A X Z ((complexClosedHomEquiv A X Z).symm (f ≫ g)) =
      complexClosedHomEquiv A X Z
      ((complexClosedHomEquiv A X Y).symm f ≫ (complexClosedHomEquiv A Y Z).symm g)
    rw [Equiv.apply_symm_apply, complexClosedHomEquiv_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
end SerrePositivity.DifferentialGraded
