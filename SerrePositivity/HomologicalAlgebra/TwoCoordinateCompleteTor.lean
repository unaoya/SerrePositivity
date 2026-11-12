module

public import SerrePositivity.HomologicalAlgebra.ScalarConeQuotientModel
public import SerrePositivity.HomologicalAlgebra.CochainCompleteTorAmplitude

/-!
# 正則な p 剰余から二座標の完全 Tor 振幅へ

## 概要
標的で p が正則な射について、mod p の振幅 c から (p,d) の完全振幅 c+1 を得る。

## 方針
標的の p のスカラー錐を通常商に比較し、d の錐の下界を一度だけ評価する。

## 規約
BS 著者版 Construction 6.1 の計算を任意の環射で行う。

## 使われ方
結晶被覆の完全 Tor 上界三と、その古典的な底変換の入力。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DifferentialGraded DerivedCompletion InfinityCategories

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：全ての半自由分解上での通常の Tor 振幅の上界。
方針：底変換した実際の複体のホモロジーを評価する。
規約：上に有界とは限らない。BS 著者版 Construction 6.1 の入力。
使われ方：正則な剰余から完全振幅へ移す。 -/
@[expose] def HasCochainTorAmplitude (f : R →+* S) (c : ℕ) : Prop :=
  ∀ (L K : CochainComplex (ModuleCat.{u} R) ℤ) (q : L ⟶ K), QuasiIso q →
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R L → ∀ (m : ℤ),
      (∀ i : ℤ, i < m → IsZero (K.homology i)) →
        ∀ i : ℤ, i < m - (c : ℤ) → IsZero ((baseChange f L).homology i)

/-- 概要：正則な p の商の通常の振幅 c から、二座標の完全振幅 c+1 を得る。
方針：K-flat な底変換上で p の錐を剰余に比較し、もう一つの錐で下界を評価する。
規約：任意の非有界入力。BS 著者版 Construction 6.1 の c=2 の計算を含む。
使われ方：完全 Tor 上界三の一般の共通部品。 -/
theorem completeTorAmplitude_two_of_modP (p : ℕ) (f : R →+* S) (d : R)
    (hp : IsSMulRegular S (p : S)) (c : ℕ)
    (hmod : HasCochainTorAmplitude
      ((Ideal.Quotient.mk (Ideal.span {(p : S)})).comp f) c) :
    HasCochainCompleteTorAmplitude f ![(p : R), d] (c + 1) := by
  intro L K q hq hL m hK i hi
  letI := hq
  let C := baseChange f L
  let qS : S →+* S ⧸ Ideal.span {(p : S)} := Ideal.Quotient.mk _
  have hC : complexKFlat S C := semifreeComplex_baseChange_isKFlat f hL
  have hCp : ∀ j : ℤ, j < m - (c : ℤ) →
      IsZero (((scalarConeFunctor (p : S)).obj C).homology j) := by
    intro j hj
    have hb := hmod L K q hq hL m hK j hj
    let e := (HomologicalComplex.homologyFunctor
      (ModuleCat.{u} (S ⧸ Ideal.span {(p : S)})) (.up ℤ) j).mapIso (baseChangeCompIso f qS L)
    have hcq : IsZero ((baseChange qS C).homology j) := hb.of_iso e
    exact scalarCone_homology_isZero_of_regular_quotient (p : S) hp C hC j hcq
  have hFirst : ∀ j : ℤ, j < m - (c : ℤ) →
      IsZero ((koszulComplexOn (Fin.init (f ∘ ![(p : R), d])) C).homology j) := by
    intro j hj
    change IsZero (((scalarConeFunctor (f (p : R))).obj C).homology j)
    let G (s : S) : Prop := IsZero (((scalarConeFunctor s).obj C).homology j)
    exact Eq.mpr (congrArg G (map_natCast f p)) (hCp j hj)
  change IsZero ((koszulComplexOn (f ∘ ![(p : R), d]) C).homology i)
  exact (Cone.exact₃ (smulId ((f ∘ ![(p : R), d]) (Fin.last 1))
    (koszulComplexOn (Fin.init (f ∘ ![(p : R), d])) C)) i (i + 1) rfl).isZero_X₂
      ((hFirst i (by omega)).eq_zero_of_src _)
      ((hFirst (i + 1) (by omega)).eq_zero_of_tgt _)

end SerrePositivity
