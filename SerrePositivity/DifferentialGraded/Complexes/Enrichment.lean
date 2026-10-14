module
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-! # 閉構造と既存 dg 豊穣構造の一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 閉構造由来の合成は U1 の Koszul 符号付き合成と同じ chain map。 -/
lemma closedComposition_eq (X Y Z : Complex A) :
    MonoidalClosed.comp X Y Z = enrichedComposition X Y Z := by
  have ht : MonoidalClosed.compTranspose X Y Z =
      (α_ X (homComplex A X Y) (homComplex A Y Z)).inv ≫
        evaluation X Y ▷ homComplex A Y Z ≫ evaluation Y Z := by
    rw [evaluation_eq, evaluation_eq]
    rfl
  apply tensorHom_ext
  intro p q m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change Homogeneous X Y p at f
  change Homogeneous Y Z q at g
  change (MonoidalClosed.comp X Y Z).f m
    (ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q m hm (f ⊗ₜ[A] g)) =
    (enrichedComposition X Y Z).f m
      (ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q m hm (f ⊗ₜ[A] g))
  rw [enrichedComposition_apply]
  apply Cochain.ext
  intro i n hin
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((tensorHomEquiv X (homComplex A X Y ⊗ homComplex A Y Z) Z
    (MonoidalClosed.compTranspose X Y Z)).f m
      (ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q m hm (f ⊗ₜ[A] g))).v i n hin x =
    ((p * q).negOnePow • f.comp g hm).v i n hin x
  rw [ht, tensorHomEquiv_component]
  change (m * i).negOnePow • (evaluation Y Z).f n
    (((evaluation X Y) ▷ homComplex A Y Z).f n
      ((α_ X (homComplex A X Y) (homComplex A Y Z)).inv.f n
        (ιTensorObj X (homComplex A X Y ⊗ homComplex A Y Z) i m n hin
          (x ⊗ₜ[A] ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q m hm
            (f ⊗ₜ[A] g))))) = _
  rw [associator_inv_apply]
  rw [whiskerRight_apply (evaluation X Y) (homComplex A Y Z)]
  rw [evaluation_apply]
  simp only [Units.smul_def]
  rw [evaluation_apply]
  simp only [Units.smul_def, map_zsmul, smul_smul]
  rw [Cochain.smul_v, Cochain.comp_v f g hm i (i + p) n rfl (by omega)]
  change ((m * i).negOnePow * (((i + p) * q).negOnePow * (i * p).negOnePow)) •
    g.v (i + p) n (by omega) (f.v i (i + p) rfl x) =
      (p * q).negOnePow • g.v (i + p) n (by omega) (f.v i (i + p) rfl x)
  simp only [← Int.negOnePow_add]
  have hdeg : m * i + ((i + p) * q + i * p) = p * q + 2 * (i * m) := by
    rw [← hm]
    ring
  rw [hdeg, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- 右単位射の斉次成分は tensor の x⊗1 を x へ送る。 -/
lemma rightUnitor_apply (X : Complex A) (i : ℤ) (x : X.X i) :
    (ρ_ X).hom.f i (ιTensorObj X (𝟙_ (Complex A)) i 0 i (add_zero i) (x ⊗ₜ[A] (1 : A))) = x := by
  have hv := congr($(rightUnitor'_inv X i).hom x)
  change (ρ_ X).inv.f i x =
    ιTensorObj X (𝟙_ (Complex A)) i 0 i (add_zero i) (x ⊗ₜ[A] (1 : A)) at hv
  have hi := congrArg (fun f => f.f i) (ρ_ X).inv_hom_id
  have hx := congr($(hi).hom x)
  change (ρ_ X).hom.f i ((ρ_ X).inv.f i x) = x at hx
  rw [hv] at hx
  exact hx

/-- 閉構造由来の単位は U1 の閉次数零単位と同じ。 -/
lemma closedIdentity_eq (X : Complex A) : MonoidalClosed.id X = identity X := by
  apply (unitCycleEquiv (homComplex A X X)).injective
  apply Subtype.ext
  change (cycleFromUnit (homComplex A X X) (MonoidalClosed.id X)).val =
    (cycleFromUnit (homComplex A X X) (identity X)).val
  rw [identity, cycleFromUnit_unitFromCycle]
  apply Cochain.ext₀
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((tensorHomEquiv X (𝟙_ (Complex A)) X (ρ_ X).hom).f 0 (1 : A)).v i i (add_zero i) x = x
  rw [tensorHomEquiv_component]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  exact rightUnitor_apply X i x
/-- Ch(A) の主豊穣構造は閉構造からの Mathlib 自己豊穣構造に一致する。 -/
lemma complexEnrichment_eq_closed :
    complexEnrichment (A := A) = MonoidalClosed.enrichedCategorySelf (Complex A) := by
  unfold complexEnrichment MonoidalClosed.enrichedCategorySelf
  congr 1
  · funext X
    exact (closedIdentity_eq X).symm
  · funext X Y Z
    exact (closedComposition_eq X Y Z).symm
end SerrePositivity.DifferentialGraded
