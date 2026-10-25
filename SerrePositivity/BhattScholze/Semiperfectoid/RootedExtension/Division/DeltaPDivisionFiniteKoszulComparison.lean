module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaPDivisionFiniteRelationsRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulCanonicalZero

/-! # 有限実p除算Koszul複体と通常商の正規化比較

標準包含からのH⁰単位を標準商射へ送る同型を用いる。
無限δ関係と導来δ基底変更の比較はここには含めない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 実有限関係族のspanは、既存の実有限段イデアル。 -/
theorem deltaPDivisionFiniteRelations_span (N : ℕ) :
    Ideal.span (Set.range fun i : Fin (N + 1) => g₀ i.val) = I₀ N := by
  have h := deltaPDivisionFiniteRelations_ofList (σ := σ) D y N
  have hs : {r : L₀ | r ∈ List.ofFn fun i : Fin (N + 1) => g₀ i.val} =
      Set.range (fun i : Fin (N + 1) => g₀ i.val) := by
    ext r
    simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
  simpa only [Ideal.ofList, hs] using h

/-- 標準H⁰単位で正規化した、実Koszul複体のH⁰と実有限通常商の線形同型。
H⁰のこの同型自体には関係列の正則性は不要。 -/
def deltaPDivisionFiniteKoszulH0Equiv (N : ℕ) :
    (SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val)).homology 0 ≃ₗ[L₀]
      L₀ ⧸ I₀ N :=
  (koszulCanonicalH0Equiv L₀ (fun i : Fin (N + 1) => g₀ i.val)).trans
    (Submodule.quotEquivOfEq _ _ (deltaPDivisionFiniteRelations_span D y N))

/-- 正規化H⁰同型は実自由環の標準単位を実有限商の標準商元へ送る。 -/
theorem deltaPDivisionFiniteKoszulH0Equiv_unit (N : ℕ) (r : L₀) :
    deltaPDivisionFiniteKoszulH0Equiv D y N
      (koszulH0Unit L₀ (fun i : Fin (N + 1) => g₀ i.val) r) =
        Ideal.Quotient.mk (I₀ N) r := by
  rw [deltaPDivisionFiniteKoszulH0Equiv, LinearEquiv.trans_apply,
    koszulCanonicalH0Equiv_unit]
  exact Submodule.quotEquivOfEq_mk _ _ _ r

/-- 正規化H⁰同型を用いた、実Koszul複体から実有限通常商への添加写像。 -/
def deltaPDivisionFiniteKoszulAugmentation (N : ℕ) :
    SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val) ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of L₀ (L₀ ⧸ I₀ N)) :=
  SerrePositivity.toSingleOfHomology _ SerrePositivity.koszulComplex_d_zero_one
    (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom

/-- 添加写像の実H⁰写像は、上で正規化した同型そのもの。 -/
theorem deltaPDivisionFiniteKoszulAugmentation_homologyMap (N : ℕ) :
    HomologicalComplex.homologyMap (deltaPDivisionFiniteKoszulAugmentation D y N) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of L₀ (L₀ ⧸ I₀ N))).hom =
      (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom :=
  SerrePositivity.toSingleOfHomology_homologyMap _ _ _

/-- 実添加写像がH⁰に誘導する写像は、標準単位上で元の標準商射と一致する。 -/
theorem deltaPDivisionFiniteKoszulAugmentation_homology_unit (N : ℕ) (r : L₀) :
    (HomologicalComplex.homologyMap (deltaPDivisionFiniteKoszulAugmentation D y N) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of L₀ (L₀ ⧸ I₀ N))).hom).hom
          (koszulH0Unit L₀ (fun i : Fin (N + 1) => g₀ i.val) r) =
      Ideal.Quotient.mk (I₀ N) r := by
  rw [deltaPDivisionFiniteKoszulAugmentation_homologyMap]
  exact deltaPDivisionFiniteKoszulH0Equiv_unit D y N r

/-- 正則一元入力では、標準単位で正規化した実有限添加写像が擬同型。
これは有限の実Koszulモデルと通常商の比較である。 -/
theorem deltaPDivisionFiniteKoszulAugmentation_quasiIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    QuasiIso (deltaPDivisionFiniteKoszulAugmentation (σ := σ) D y N) := by
  apply SerrePositivity.quasiIso_toSingleOfHomology
  exact (deltaPDivisionFiniteRelations_isKoszulResolution D y hpA hg v hv hy N).isZero

end SerrePositivity.BhattScholze
