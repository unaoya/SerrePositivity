module

public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import Mathlib.RingTheory.Localization.BaseChange

/-! # 標準局所化後のエタール性の任意の基底変更

A[1/g]→B[1/g] のエタール性を、任意の A 代数 R に対する
R[1/g]→(R⊗_A B)[1/g] のエタール性へ移す。局所化とテンソル積の実際の代数同型、
エタール性の合成・基底変更・係数制限を使う。
平坦性、Noether 性、整域性、有限性の追加仮定は必要ない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.GenericEtale
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable (A R B : Type u) [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra A B]

/-- 標準局所化後のエタール性は、任意の基底変更により保たれる。
両側の局所化上の作用は awayAlgebra で明示する。 -/
theorem etale_away_baseChange (g : A) :
    let _ := awayAlgebra A B g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A B g)) →
      let _ := awayAlgebra R (R ⊗[A] B) (algebraMap A R g)
      Algebra.Etale (Localization.Away (algebraMap A R g))
        (Localization.Away (algebraMap R (R ⊗[A] B) (algebraMap A R g))) := by
  let := awayAlgebra A B g
  dsimp only
  intro h
  let : Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A B g)) := h
  let : IsScalarTower A (Localization.Away g) (Localization.Away (algebraMap A B g)) :=
    awayAlgebra_scalarTower A B g
  let : Algebra.Etale A (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  let : Algebra.Etale A (Localization.Away (algebraMap A B g)) :=
    Algebra.Etale.comp A (Localization.Away g) (Localization.Away (algebraMap A B g))
  let e := IsLocalization.Away.tensorProductEquivTMulRight A R (algebraMap A B g)
    (Localization.Away (algebraMap A B g))
  have ht : Algebra.Etale R (Localization.Away ((1 : R) ⊗ₜ[A] algebraMap A B g)) :=
    Algebra.Etale.of_equiv e
  have heq : algebraMap R (R ⊗[A] B) (algebraMap A R g) =
      (1 : R) ⊗ₜ[A] algebraMap A B g := by
    rw [← IsScalarTower.algebraMap_apply A R (R ⊗[A] B),
      Algebra.TensorProduct.algebraMap_apply']
  rw [← heq] at ht
  let := awayAlgebra R (R ⊗[A] B) (algebraMap A R g)
  let : IsScalarTower R (Localization.Away (algebraMap A R g))
      (Localization.Away (algebraMap R (R ⊗[A] B) (algebraMap A R g))) :=
    awayAlgebra_scalarTower R (R ⊗[A] B) (algebraMap A R g)
  let : Algebra.Etale R (Localization.Away (algebraMap A R g)) :=
    Algebra.Etale.of_isLocalizationAway (algebraMap A R g)
  let : Algebra.Etale R
      (Localization.Away (algebraMap R (R ⊗[A] B) (algebraMap A R g))) := ht
  exact Algebra.Etale.of_restrictScalars R (Localization.Away (algebraMap A R g)) _

/-- 有限表示な代数では、g の局所化上のエタール性は (g) の各元の局所化へ移る。
basicOpen(x)⊆basicOpen(g) を使い、エタール軌跡の判定から導く。 -/
theorem etale_away_of_mem_span_singleton
    (R₀ S : Type u) [CommRing R₀] [CommRing S] [Algebra R₀ S]
    [Algebra.FinitePresentation R₀ S] (g x : R₀) (hx : x ∈ Ideal.span {g}) :
    let _ := awayAlgebra R₀ S g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R₀ S g)) →
      let _ := awayAlgebra R₀ S x
      Algebra.Etale (Localization.Away x) (Localization.Away (algebraMap R₀ S x)) := by
  let := awayAlgebra R₀ S g
  dsimp only
  intro h
  let : Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R₀ S g)) := h
  let : IsScalarTower R₀ (Localization.Away g) (Localization.Away (algebraMap R₀ S g)) :=
    awayAlgebra_scalarTower R₀ S g
  let : Algebra.Etale R₀ (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  let : Algebra.Etale R₀ (Localization.Away (algebraMap R₀ S g)) :=
    Algebra.Etale.comp R₀ (Localization.Away g) (Localization.Away (algebraMap R₀ S g))
  have hopen : (PrimeSpectrum.basicOpen (algebraMap R₀ S x) : Set (PrimeSpectrum S)) ⊆
      PrimeSpectrum.basicOpen (algebraMap R₀ S g) := by
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  have hetale : Algebra.Etale R₀ (Localization.Away (algebraMap R₀ S x)) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp (hopen.trans
      (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr inferInstance))
  let := awayAlgebra R₀ S x
  let : IsScalarTower R₀ (Localization.Away x) (Localization.Away (algebraMap R₀ S x)) :=
    awayAlgebra_scalarTower R₀ S x
  let : Algebra.Etale R₀ (Localization.Away x) := Algebra.Etale.of_isLocalizationAway x
  let : Algebra.Etale R₀ (Localization.Away (algebraMap R₀ S x)) := hetale
  exact Algebra.Etale.of_restrictScalars R₀ (Localization.Away x) _

/-- 基底変更後、像 g が生成する主イデアルの全ての元の反転後にエタールとなる。
有限表示性だけを追加し、任意の基底変更 R に平坦性や Noether 性を要求しない。 -/
theorem etale_away_baseChange_of_mem_span_singleton [Algebra.FinitePresentation A B]
    (g : A) (x : R) (hx : x ∈ Ideal.span {algebraMap A R g}) :
    let _ := awayAlgebra A B g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A B g)) →
      let _ := awayAlgebra R (R ⊗[A] B) x
      Algebra.Etale (Localization.Away x)
        (Localization.Away (algebraMap R (R ⊗[A] B) x)) := by
  let := awayAlgebra A B g
  dsimp only
  intro h
  exact etale_away_of_mem_span_singleton R (R ⊗[A] B) (algebraMap A R g) x hx
    (etale_away_baseChange A R B g h)

end SerrePositivity.GenericEtale
