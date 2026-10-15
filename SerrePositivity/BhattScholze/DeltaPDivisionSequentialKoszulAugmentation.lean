module

public import SerrePositivity.BhattScholze.DeltaPDivisionFiniteQuotientColimit

/-! # raw δ包への実無限Koszul添加写像

実有限Koszul図式の圏論的colimitを用い、その実H⁰からraw δ包へ写す。
原典の導来δpushout・導来完備化・CFFとの比較とは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "F₀" => deltaPDivisionFiniteKoszulDiagram (σ := σ) D y

/-- 実Koszul逐次極限の正次数の項は零。関係列の正則性は不要。 -/
theorem deltaPDivisionSequentialKoszul_isZero_X (i : ℤ) (hi : 0 < i) :
    IsZero ((colimit F₀).X i) := by
  have hz : IsZero (colimit (F₀ ⋙ eval (ModuleCat.{u} L₀) (.up ℤ) i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro N
    exact (SerrePositivity.koszulComplex_isZero_X_of_pos
      (fun j : Fin (N + 1) => g₀ j.val) i hi).eq_of_src _ _
  exact hz.of_iso (preservesColimitIso (eval (ModuleCat.{u} L₀) (.up ℤ) i) F₀)

/-- 実Koszul逐次極限の零次から一次への微分は零。 -/
theorem deltaPDivisionSequentialKoszul_d_zero_one :
    (colimit F₀).d 0 1 = 0 :=
  (deltaPDivisionSequentialKoszul_isZero_X D y 1 (by decide)).eq_of_tgt _ _

/-- raw δ包への実無限Koszul添加写像。H⁰に実raw比較同型を用いる。 -/
def deltaPDivisionSequentialKoszulAugmentation :
    colimit F₀ ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀)) :=
  SerrePositivity.toSingleOfHomology _ (deltaPDivisionSequentialKoszul_d_zero_one D y)
    (deltaPDivisionSequentialKoszulH0RawIso D y).hom

/-- 添加写像のH⁰は、実極限比較により得たraw δ包との同型。 -/
theorem deltaPDivisionSequentialKoszulAugmentation_homologyMap :
    homologyMap (deltaPDivisionSequentialKoszulAugmentation (σ := σ) D y) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀))).hom =
      (deltaPDivisionSequentialKoszulH0RawIso D y).hom :=
  SerrePositivity.toSingleOfHomology_homologyMap _ _ _

/-- 正則一元入力では、raw δ包への実無限Koszul添加写像は擬同型。 -/
theorem deltaPDivisionSequentialKoszulAugmentation_quasiIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    QuasiIso (deltaPDivisionSequentialKoszulAugmentation (σ := σ) D y) := by
  apply SerrePositivity.quasiIso_toSingleOfHomology
  exact deltaPDivisionSequentialKoszul_isZero_homology D y hpA hg v hv hy

end SerrePositivity.BhattScholze
