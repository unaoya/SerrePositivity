module

public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Smooth.Flat
public import SerrePositivity.CommutativeAlgebra.Localization.Away
public import SerrePositivity.CommutativeAlgebra.ReducedSpectrum
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.Pi

/-! # 主開集合上の有限 étale 代数の階数による分解

## 概要

有限 `R` 代数 `S` と `g : R` で、`S[1/g]` が `R[1/g]` 上有限 étale なものについて、`D(g)` 上の階数 `awayRank`（`S[1/g]` の茎の階数を同相 `Spec R[1/g] ≃ D(g)` で移したもの）が局所定数で、有限個の開閉集合 `rankOpen n` に分かれることを示す。各 `rankOpen n` の切断への `R` の像 `R_n`（`openSectionImage`）の有限性・核・スペクトルの像（閉包）、`rankOpen n` の `R[1/g]` の冪等元による主開表示、有限直積 `R → ∏ R_n`（`toRankImageProduct`）の核とスペクトルの像、`g` を反転すると全単射になること、`R_n` を通る基底変更の後も階数が一定であることを与える。

## 方針

階数の局所定数性と基底変更は Mathlib の `Module.rankAtStalk` の一般論を `D(g)` へ移して使う。直積の全単射性はスペクトルの有限分割と中国剰余定理による。

## 規約

perfectoid 化や BS Cor 8.12 は使わない。CLMST（Cai–Lee–Ma–Schwede–Tucker, arXiv:2209.04046）Prop 2.4.7 の証明の、階数ごとの分解の部分（原典の `R_i`）。旧 `CLMST/Prop247Rank*` の 7 本で、宣言名の接頭辞 `prop247_` を外した。

## 使われ方

CLMST の `PerfectoidizationIsogeny`（Prop 2.4.7）の階数による帰着。
-/

@[expose] public noncomputable section

universe u

section RankLociPart

namespace SerrePositivity

/-- 元の局所化写像による Spec R[1/g] と D(g) の同相。 -/
def awaySpectrumHomeomorph (R : Type u) [CommRing R] (g : R) :
    PrimeSpectrum (Localization.Away g) ≃ₜ (PrimeSpectrum.basicOpen g) :=
  (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away g) g).isEmbedding.toHomeomorph
    |>.trans (Homeomorph.setCongr
      (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g))

/-- 同相の点への作用は元の局所化環写像の comap そのものである。 -/
@[simp] theorem awaySpectrumHomeomorph_apply
    (R : Type u) [CommRing R] (g : R) (x : PrimeSpectrum (Localization.Away g)) :
    ((awaySpectrumHomeomorph R g x) : PrimeSpectrum R) =
      PrimeSpectrum.comap (algebraMap R (Localization.Away g)) x := rfl

/-- D(g) 上の rank は、元の S[1/g] の局所加群の rank である。 -/
def awayRank (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (g : R) : (PrimeSpectrum.basicOpen g) → ℕ := by
  letI := GenericEtale.awayAlgebra R S g
  exact fun x => Module.rankAtStalk (R := Localization.Away g)
    (Localization.Away (algebraMap R S g)) ((awaySpectrumHomeomorph R g).symm x)

/-- 元の局所化の各点で、D(g) に移した rank は元の stalk rank に一致する。 -/
@[simp] theorem awayRank_at_localization
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (g : R) (x : PrimeSpectrum (Localization.Away g)) :
    letI := GenericEtale.awayAlgebra R S g
    awayRank R S g (awaySpectrumHomeomorph R g x) =
      Module.rankAtStalk (R := Localization.Away g)
        (Localization.Away (algebraMap R S g)) x := by
  letI := GenericEtale.awayAlgebra R S g
  simp only [awayRank, Homeomorph.symm_apply_apply]

/-- 有限 étale な実局所化代数の rank は D(g) 上で局所定数である。 -/
theorem awayRank_isLocallyConstant
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (g : R) :
    letI := GenericEtale.awayAlgebra R S g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)) →
      IsLocallyConstant (awayRank R S g) := by
  letI := GenericEtale.awayAlgebra R S g
  intro hetale
  letI := hetale
  letI := GenericEtale.finite_away R S g
  letI := Module.FinitePresentation.of_finite_of_finitePresentation
    (Localization.Away g) (Localization.Away (algebraMap R S g))
  exact (Module.isLocallyConstant_rankAtStalk
    (R := Localization.Away g) (M := Localization.Away (algebraMap R S g))).comp_continuous
      (awaySpectrumHomeomorph R g).symm.continuous

/-- 原典の rank 別開閉部分は有限個で D(g) を被覆し、互いに素である。
rank 0 および D(g) が空の場合を含む。 -/
theorem awayRank_finite_clopen_decomposition
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (g : R) :
    letI := GenericEtale.awayAlgebra R S g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)) →
      ∃ t : Finset ℕ,
        (∀ n, n ∈ t ↔ ∃ x, awayRank R S g x = n) ∧
        (∀ n, IsClopen {x | awayRank R S g x = n}) ∧
        (∀ x, awayRank R S g x ∈ t) ∧
        (∀ n m : ℕ, n ≠ m → Disjoint
          {x | awayRank R S g x = n} {x | awayRank R S g x = m}) := by
  letI := GenericEtale.awayAlgebra R S g
  intro hetale
  classical
  letI : CompactSpace (PrimeSpectrum.basicOpen g) :=
    isCompact_iff_compactSpace.mp (PrimeSpectrum.isCompact_basicOpen g)
  have h := awayRank_isLocallyConstant R S g hetale
  let t := h.range_finite.toFinset
  refine ⟨t, ?_, h.isClopen_fiber, ?_, ?_⟩
  · intro n
    exact Set.Finite.mem_toFinset _
  · intro x
    exact h.range_finite.mem_toFinset.mpr ⟨x, rfl⟩
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hn hm
    exact hnm (hn.symm.trans hm)

end SerrePositivity

end RankLociPart

section RankTransportPart

namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- g が可逆な底変換環の元の点の rank は、元の D(g) の対応点の rank と一致する。 -/
theorem rankAtStalk_baseChange_on_away_point
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (T : Type u) [CommRing T] [Algebra R T] (hg : IsUnit (algebraMap R T g))
    (x : PrimeSpectrum T) (y : PrimeSpectrum.basicOpen g)
    (hy : (y : PrimeSpectrum R) = x.comap (algebraMap R T)) :
    Module.rankAtStalk (R := T) (T ⊗[R] S) x = awayRank R S g y := by
  let A := Localization.Away g
  let M := Localization.Away (algebraMap R S g)
  letI := GenericEtale.awayAlgebra R S g
  letI : IsScalarTower R A M := GenericEtale.awayAlgebra_scalarTower R S g
  let l : A →ₐ[R] T := IsLocalization.Away.liftAlgHom g (f := Algebra.ofId R T) hg
  letI : Algebra A T := l.toRingHom.toAlgebra
  letI : IsScalarTower R A T := IsScalarTower.of_algHom l
  letI : Algebra.Etale A M := hetale
  letI : Module.Finite A M := GenericEtale.finite_away R S g
  let e : T ⊗[R] S ≃ₐ[T] T ⊗[A] M :=
    (Algebra.TensorProduct.cancelBaseChange R A T T S).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) (originalAwayTensorEquiv R S g))
  let q := x.comap (algebraMap A T)
  have hq : awaySpectrumHomeomorph R g q = y := by
    apply Subtype.ext
    rw [awaySpectrumHomeomorph_apply]
    change PrimeSpectrum.comap (algebraMap R A)
      (PrimeSpectrum.comap (algebraMap A T) x) = (y : PrimeSpectrum R)
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq R A T]
    exact hy.symm
  calc
    Module.rankAtStalk (R := T) (T ⊗[R] S) x =
        Module.rankAtStalk (R := T) (T ⊗[A] M) x :=
      congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) x
    _ = Module.rankAtStalk (R := A) M q := Module.rankAtStalk_baseChange (M := M) x
    _ = awayRank R S g y := by
      rw [← hq]
      exact (awayRank_at_localization R S g q).symm

/-- 元の D(g) 上の定 rank は、任意の実通常底変換の D(g) 上で保存される。 -/
theorem awayRank_baseChange_constant
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (r : ℕ) (hRank : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x = r) :
    ∀ x : PrimeSpectrum.basicOpen (algebraMap R B g),
      awayRank B (B ⊗[R] S) (algebraMap R B g) x = r := by
  let A := B ⊗[R] S
  let d := algebraMap R B g
  let L := Localization.Away d
  let M := Localization.Away (algebraMap B A d)
  letI := GenericEtale.awayAlgebra B A d
  letI : IsScalarTower B L M := GenericEtale.awayAlgebra_scalarTower B A d
  have hg : IsUnit (algebraMap R L g) := by
    rw [IsScalarTower.algebraMap_apply R B L]
    exact IsLocalization.Away.algebraMap_isUnit (S := L) d
  let e : M ≃ₐ[L] L ⊗[R] S := (originalAwayTensorEquiv B A d).symm.trans
    (Algebra.TensorProduct.cancelBaseChange R B L L S)
  intro x
  let z := (awaySpectrumHomeomorph B d).symm x
  have hz : algebraMap R L g ∉ z.asIdeal := fun h =>
    z.isPrime.ne_top (z.asIdeal.eq_top_of_isUnit_mem h hg)
  let y : PrimeSpectrum.basicOpen g := ⟨z.comap (algebraMap R L), hz⟩
  change Module.rankAtStalk (R := L) M z = r
  calc
    Module.rankAtStalk (R := L) M z = Module.rankAtStalk (R := L) (L ⊗[R] S) z :=
      congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) z
    _ = awayRank R S g y :=
      rankAtStalk_baseChange_on_away_point R S g hetale L hg z y rfl
    _ = r := hRank y

end SerrePositivity

end RankTransportPart

section RankImagesPart

namespace SerrePositivity
open TopologicalSpace Opposite AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の R→Γ(U,O) の像の環。 -/
abbrev openSectionImage (R : Type u) [CommRing R] (U : Opens (PrimeSpectrum R)) : Type u :=
  (Algebra.ofId R ((Spec.structureSheaf R).obj.obj (op U))).range

/-- 切断への元の写像を像に制限した実環写像。 -/
abbrev toOpenSectionImage (R : Type u) [CommRing R] (U : Opens (PrimeSpectrum R)) :
    R →ₐ[R] openSectionImage R U :=
  (Algebra.ofId R ((Spec.structureSheaf R).obj.obj (op U))).rangeRestrict

theorem toOpenSectionImage_surjective
    (R : Type u) [CommRing R] (U : Opens (PrimeSpectrum R)) :
    Function.Surjective (toOpenSectionImage R U) :=
  AlgHom.rangeRestrict_surjective _

/-- 原典の像の環は R の商であり、R 上有限である。 -/
theorem openSectionImage_finite
    (R : Type u) [CommRing R] (U : Opens (PrimeSpectrum R)) :
    Module.Finite R (openSectionImage R U) :=
  Module.Finite.of_surjective (toOpenSectionImage R U).toLinearMap
    (toOpenSectionImage_surjective R U)

/-- 被約な基底では、像への元の写像の核は開集合の消滅イデアルである。 -/
theorem toOpenSectionImage_ker
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) :
    RingHom.ker (toOpenSectionImage R U).toRingHom =
      PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R)) :=
  (AlgHom.ker_rangeRestrict (Algebra.ofId R ((Spec.structureSheaf R).obj.obj (op U)))).trans
    (ker_algebraMap_sections_eq_vanishingIdeal R U)

/-- 閉包の消滅イデアルによる商と、原典の切断への像との同型。 -/
def openSectionImageQuotientEquiv
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) :
    (R ⧸ PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R))) ≃ₐ[R]
      openSectionImage R U :=
  (Ideal.quotientEquivAlgOfEq R (ker_algebraMap_sections_eq_vanishingIdeal R U).symm).trans
    (Ideal.quotientKerEquivRange (Algebra.ofId R ((Spec.structureSheaf R).obj.obj (op U))))

/-- 同型は元の R の各元を元の像の元に送る。 -/
@[simp] theorem openSectionImageQuotientEquiv_mk
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) (r : R) :
    openSectionImageQuotientEquiv R U (Ideal.Quotient.mk _ r) =
      toOpenSectionImage R U r :=
  (openSectionImageQuotientEquiv R U).commutes r

/-- 原典の像の環の Spec の像は、実開集合 U の閉包である。 -/
theorem openSectionImage_spectrum_range
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) :
    Set.range (PrimeSpectrum.comap (toOpenSectionImage R U).toRingHom) =
      closure (U : Set (PrimeSpectrum R)) := by
  rw [range_comap_of_surjective _ _ (toOpenSectionImage_surjective R U),
    toOpenSectionImage_ker, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]

/-- rank 別の相対開閉部分を、Spec R の実開集合として固定する。 -/
def rankOpen
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (n : ℕ) : Opens (PrimeSpectrum R) :=
  ⟨Subtype.val '' {x | awayRank R S g x = n},
    (PrimeSpectrum.isOpen_basicOpen (a := g)).isOpenMap_subtype_val _
      ((awayRank_isLocallyConstant R S g hetale).isOpen_fiber n)⟩

/-- rank 部分の閉包を D(g) に戻すと、元の rank 部分に一致する。 -/
theorem rankOpen_closure_on_away
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    (Subtype.val : (PrimeSpectrum.basicOpen g) → PrimeSpectrum R) ⁻¹'
      closure (rankOpen R S g hetale n : Set (PrimeSpectrum R)) =
      {x | awayRank R S g x = n} :=
  (PrimeSpectrum.isOpen_basicOpen (a := g)).isOpenMap_subtype_val.preimage_closure_image
    Subtype.val_injective continuous_subtype_val _
    ((awayRank_isLocallyConstant R S g hetale).isClosed_fiber n)

/-- 原典の Ri=im(R→Γ(Ui,O)) の Spec は、g の外で元の rank 部分をちょうど表す。 -/
theorem rankSectionImage_spectrum_on_away
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    (Subtype.val : (PrimeSpectrum.basicOpen g) → PrimeSpectrum R) ⁻¹'
      Set.range (PrimeSpectrum.comap
        (toOpenSectionImage R (rankOpen R S g hetale n)).toRingHom) =
      {x | awayRank R S g x = n} := by
  rw [openSectionImage_spectrum_range, rankOpen_closure_on_away]

end SerrePositivity

end RankImagesPart

section RankPrincipalPart

namespace SerrePositivity

/-- 各実 rank 部分は g の倍数による主開集合である。空の部分も含む。 -/
theorem rankOpen_exists_basicOpen
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    ∃ a : R, rankOpen R S g hetale n = PrimeSpectrum.basicOpen (g * a) := by
  let H := awaySpectrumHomeomorph R g
  have hc : IsClopen {y : PrimeSpectrum (Localization.Away g) |
      awayRank R S g (H y) = n} :=
    ((awayRank_isLocallyConstant R S g hetale).isClopen_fiber n).preimage
      H.continuous
  obtain ⟨e, _he, he⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hc
  let v := IsLocalization.Away.sec g e
  have hv : algebraMap R (Localization.Away g) (g * v.1) =
      (algebraMap R (Localization.Away g) g) ^ (v.2 + 1) * e := by
    dsimp only [v]
    rw [map_mul, ← IsLocalization.Away.sec_spec g e, map_pow, pow_succ]
    ac_rfl
  have hm (y : PrimeSpectrum (Localization.Away g)) :
      PrimeSpectrum.comap (algebraMap R (Localization.Away g)) y ∈
        PrimeSpectrum.basicOpen (g * v.1) ↔ y ∈ PrimeSpectrum.basicOpen e := by
    change algebraMap R (Localization.Away g) (g * v.1) ∉ y.asIdeal ↔ e ∉ y.asIdeal
    rw [hv]
    exact not_congr (y.asIdeal.unit_mul_mem_iff_mem
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow (v.2 + 1)))
  have hr (y : PrimeSpectrum (Localization.Away g)) :
      awayRank R S g (H y) = n ↔ y ∈ PrimeSpectrum.basicOpen e :=
    Set.ext_iff.mp he y
  refine ⟨v.1, ?_⟩
  apply TopologicalSpace.Opens.ext
  ext x
  change x ∈ Subtype.val '' {z | awayRank R S g z = n} ↔
    x ∈ PrimeSpectrum.basicOpen (g * v.1)
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := (hm (H.symm z)).mpr ((hr (H.symm z)).mp (by simpa using hz))
    simpa only [← awaySpectrumHomeomorph_apply, H, Homeomorph.apply_symm_apply] using hz'
  · intro hx
    let z : PrimeSpectrum.basicOpen g :=
      ⟨x, PrimeSpectrum.basicOpen_mul_le_left g v.1 hx⟩
    refine ⟨z, ?_, rfl⟩
    have hx' : PrimeSpectrum.comap (algebraMap R (Localization.Away g)) (H.symm z) ∈
        PrimeSpectrum.basicOpen (g * v.1) := by
      simpa only [← awaySpectrumHomeomorph_apply, H, Homeomorph.apply_symm_apply]
        using hx
    have hz' := (hr (H.symm z)).mpr ((hm (H.symm z)).mp hx')
    simpa only [Set.mem_ofPred_eq, Homeomorph.apply_symm_apply] using hz'

end SerrePositivity

end RankPrincipalPart

section RankProductPart

namespace SerrePositivity
open TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ)

/-- 原典の各切断への像の環の有限直積。空の直積も許す。 -/
abbrev rankImageProduct : Type u :=
  (n : t) → openSectionImage R (rankOpen R S g hetale n)

/-- 元の R の元を、各 rank 部分の元の切断の像へ送る写像。 -/
def toRankImageProduct : R →ₐ[R] rankImageProduct R S g hetale t :=
  AlgHom.pi (fun n => toOpenSectionImage R (rankOpen R S g hetale n))

/-- 有限直積への写像は有限な環写像である。Ri の有限表示性は要求しない。 -/
theorem rankImageProduct_finite :
    Module.Finite R (rankImageProduct R S g hetale t) := by
  letI (n : t) : Module.Finite R
      (openSectionImage R (rankOpen R S g hetale n)) :=
    openSectionImage_finite R _
  infer_instance

/-- 元の rank 分解の有限集合が与えられれば、その実開集合の和は D(g) である。 -/
theorem rankOpen_iUnion
    (ht : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x ∈ t) :
    (⋃ n : t, (rankOpen R S g hetale n : Set (PrimeSpectrum R))) =
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨n, y, _hy, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨awayRank R S g ⟨x, hx⟩, ht ⟨x, hx⟩⟩, ⟨x, hx⟩, rfl, rfl⟩

/-- 被約基底では、有限直積の Spec の実像は D(g) の閉包である。 -/
theorem rankImageProduct_spectrum_range [IsReduced R]
    (ht : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x ∈ t) :
    Set.range (PrimeSpectrum.comap (toRankImageProduct R S g hetale t).toRingHom) =
      closure (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  rw [← PrimeSpectrum.iUnion_range_comap_comp_evalRingHom
    (toRankImageProduct R S g hetale t).toRingHom]
  change (⋃ n : t, Set.range (PrimeSpectrum.comap
    (toOpenSectionImage R (rankOpen R S g hetale n)).toRingHom)) = _
  simp_rw [openSectionImage_spectrum_range]
  rw [← closure_iUnion_of_finite, rankOpen_iUnion R S g hetale t ht]

/-- 有限直積への元の写像の核は D(g) の消滅イデアルである。 -/
theorem toRankImageProduct_ker [IsReduced R]
    (ht : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x ∈ t) :
    RingHom.ker (toRankImageProduct R S g hetale t).toRingHom =
      PrimeSpectrum.vanishingIdeal (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  ext a
  change (fun n : t => toOpenSectionImage R
    (rankOpen R S g hetale n) a) = 0 ↔ _
  have hn (n : t) : toOpenSectionImage R
      (rankOpen R S g hetale n) a = 0 ↔
      ∀ x ∈ (rankOpen R S g hetale n), a ∈ x.asIdeal := by
    change a ∈ RingHom.ker (toOpenSectionImage R
      (rankOpen R S g hetale n)).toRingHom ↔ _
    rw [toOpenSectionImage_ker, PrimeSpectrum.mem_vanishingIdeal]
    rfl
  rw [PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h x hx
    let n : t := ⟨awayRank R S g ⟨x, hx⟩, ht ⟨x, hx⟩⟩
    exact (hn n).mp (congrFun h n) x ⟨⟨x, hx⟩, rfl, rfl⟩
  · intro h
    funext n
    apply (hn n).mpr
    rintro x ⟨y, _hy, rfl⟩
    exact h y.1 y.2

end SerrePositivity

end RankProductPart

section RankProductAwayPart

namespace SerrePositivity
open TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))

/-- 原典の像への写像 R→Ri を g で局所化した元の環写像。 -/
abbrev awayToRankImage (n : ℕ) :=
  Localization.awayMap
    (toOpenSectionImage R (rankOpen R S g hetale n)).toRingHom g

theorem awayToRankImage_surjective (n : ℕ) :
    Function.Surjective (awayToRankImage R S g hetale n) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective g
    (toOpenSectionImage_surjective R _)

/-- 各元の局所化写像の Spec の像は、元の局所化上の所定の rank ファイバーである。 -/
theorem awayToRankImage_spectrum_range [IsReduced R] (n : ℕ) :
    Set.range (PrimeSpectrum.comap (awayToRankImage R S g hetale n)) =
      {x | awayRank R S g (awaySpectrumHomeomorph R g x) = n} := by
  let U := rankOpen R S g hetale n
  let q := (toOpenSectionImage R U).toRingHom
  have hker : RingHom.ker (awayToRankImage R S g hetale n) =
      (PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R))).map
        (algebraMap R (Localization.Away g)) := by
    have hk := IsLocalization.ker_map (S := Localization.Away g) (Localization.Away (q g)) q
      (Submonoid.map_powers q g)
    rw [show RingHom.ker q = PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R)) from
      toOpenSectionImage_ker R U] at hk
    exact hk
  ext x
  rw [range_comap_of_surjective _ _ (awayToRankImage_surjective R S g hetale n), hker]
  change ((PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R))).map
    (algebraMap R (Localization.Away g))) ≤ x.asIdeal ↔ _
  rw [Ideal.map_le_iff_le_comap]
  change PrimeSpectrum.comap (algebraMap R (Localization.Away g)) x ∈
    PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R)) : Set R) ↔ _
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have h := congrArg (fun Z => awaySpectrumHomeomorph R g x ∈ Z)
    (rankOpen_closure_on_away R S g hetale n)
  simpa only [Set.mem_preimage, awaySpectrumHomeomorph_apply, Set.mem_ofPred_eq]
    using Iff.of_eq h

/-- 元の有限直積写像を各成分で g に局所化すると全単射になる。
大域的な直積写像そのものの単射性・全射性は要求しない。 -/
theorem awayRankImageProduct_bijective [IsReduced R] (t : Finset ℕ)
    (ht : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x ∈ t) :
    Function.Bijective (RingHom.pi (fun n : t => awayToRankImage R S g hetale n)) := by
  apply pi_ringHom_bijective_of_spectrum_partition (Localization.Away g)
    (fun n : t => Localization.Away
      ((toOpenSectionImage R (rankOpen R S g hetale n)) g))
    (fun n : t => awayToRankImage R S g hetale n)
    (fun n => awayToRankImage_surjective R S g hetale n)
  · intro i j hij
    rw [awayToRankImage_spectrum_range, awayToRankImage_spectrum_range]
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (Subtype.ext (hi.symm.trans hj))
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨⟨awayRank R S g (awaySpectrumHomeomorph R g x),
      ht (awaySpectrumHomeomorph R g x)⟩, ?_⟩
    rw [awayToRankImage_spectrum_range]
    rfl

/-- 各成分の局所化の積との標準比較を介して、元の R→∏Ri 自体の局所化が全単射となる。 -/
theorem toRankImageProduct_away_bijective [IsReduced R] (t : Finset ℕ)
    (ht : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x ∈ t) :
    Function.Bijective (Localization.awayMap
      (toRankImageProduct R S g hetale t).toRingHom g) := by
  let A := fun n : t => openSectionImage R (rankOpen R S g hetale n)
  let q := (toRankImageProduct R S g hetale t).toRingHom
  let B := fun n : t => Localization.Away
    ((toOpenSectionImage R (rankOpen R S g hetale n)) g)
  let M := Submonoid.powers (q g)
  letI (n : t) : IsLocalization (M.map (Pi.evalRingHom A n)) (B n) := by
    dsimp only [M]
    rw [Submonoid.map_powers]
    change IsLocalization
      (.powers ((toOpenSectionImage R (rankOpen R S g hetale n)) g))
      (Localization.Away ((toOpenSectionImage R (rankOpen R S g hetale n)) g))
    infer_instance
  letI : IsLocalization M ((n : t) → B n) :=
    (IsLocalization.iff_map_piEvalRingHom A ((n : t) → B n) M).mpr inferInstance
  let j := IsLocalization.algEquiv M (Localization.Away (q g)) ((n : t) → B n)
  have hs : j.toRingHom.comp (Localization.awayMap q g) =
      RingHom.pi (fun n : t => awayToRankImage R S g hetale n) := by
    apply IsLocalization.ringHom_ext (.powers g)
    ext r n
    change j (Localization.awayMap q g (algebraMap R (Localization.Away g) r)) n = _
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, j.commutes]
    change algebraMap (A n) (B n) (q r n) =
      awayToRankImage R S g hetale n (algebraMap R (Localization.Away g) r)
    rw [awayToRankImage, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  have hb := awayRankImageProduct_bijective R S g hetale t ht
  constructor
  · intro x y h
    apply hb.1
    rw [← hs]
    exact congrArg j h
  · intro y
    obtain ⟨x, hx⟩ := hb.2 (j y)
    refine ⟨x, j.injective ?_⟩
    change (j.toRingHom.comp (Localization.awayMap q g)) x = j y
    rwa [hs]

end SerrePositivity

end RankProductAwayPart

section RankBaseChangePart

namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Ri 上の任意の実基底変更の g の外の点は、元の rank 部分の点に写る。 -/
theorem awayRank_of_point_over_rankImage
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (openSectionImage R (rankOpen R S g hetale n)) T]
    [IsScalarTower R (openSectionImage R (rankOpen R S g hetale n)) T]
    (x : PrimeSpectrum T) (hx : algebraMap R T g ∉ x.asIdeal) :
    awayRank R S g ⟨x.comap (algebraMap R T), hx⟩ = n := by
  let I := openSectionImage R (rankOpen R S g hetale n)
  have hr : (⟨x.comap (algebraMap R T), hx⟩ : PrimeSpectrum.basicOpen g) ∈
      (Subtype.val : (PrimeSpectrum.basicOpen g) → PrimeSpectrum R) ⁻¹'
        Set.range (PrimeSpectrum.comap
          (toOpenSectionImage R (rankOpen R S g hetale n)).toRingHom) := by
    refine ⟨x.comap (algebraMap I T), ?_⟩
    change PrimeSpectrum.comap (algebraMap R I)
      (PrimeSpectrum.comap (algebraMap I T) x) = PrimeSpectrum.comap (algebraMap R T) x
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq R I T]
  rw [rankSectionImage_spectrum_on_away] at hr
  exact hr

/-- 任意の Ri 代数 T で g が可逆なら、元の T⊗R S の全ての stalk rank は n である。
元の S の R 上の平坦性や T の平坦性は仮定しない。 -/
theorem rankAtStalk_baseChange_of_isUnit
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (openSectionImage R (rankOpen R S g hetale n)) T]
    [IsScalarTower R (openSectionImage R (rankOpen R S g hetale n)) T]
    (hg : IsUnit (algebraMap R T g)) (x : PrimeSpectrum T) :
    Module.rankAtStalk (R := T) (T ⊗[R] S) x = n := by
  have hx : algebraMap R T g ∉ x.asIdeal := fun h =>
    x.2.ne_top (x.asIdeal.eq_top_of_isUnit_mem h hg)
  calc
    Module.rankAtStalk (R := T) (T ⊗[R] S) x =
        awayRank R S g ⟨x.comap (algebraMap R T), hx⟩ :=
      rankAtStalk_baseChange_on_away_point R S g hetale T hg x _ rfl
    _ = n := awayRank_of_point_over_rankImage R S g hetale n T x hx

/-- 任意の Ri 代数 T に対し、元の底変換 T⊗R S の rank は D(g) 上で一定である。
指定した (Ri)_perfd への適用にも、T の平坦性や g 正則性を要求しない。 -/
theorem awayRank_baseChange_over_rankImage
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (openSectionImage R (rankOpen R S g hetale n)) T]
    [IsScalarTower R (openSectionImage R (rankOpen R S g hetale n)) T]
    (x : PrimeSpectrum.basicOpen (algebraMap R T g)) :
    awayRank T (T ⊗[R] S) (algebraMap R T g) x = n := by
  let I := openSectionImage R (rankOpen R S g hetale n)
  let d := algebraMap R T g
  let L := Localization.Away d
  letI := GenericEtale.awayAlgebra T (T ⊗[R] S) d
  let e : L ⊗[R] S ≃ₐ[L]
      Localization.Away (algebraMap T (T ⊗[R] S) d) :=
    (Algebra.TensorProduct.cancelBaseChange R T L L S).symm.trans
      (originalAwayTensorEquiv T (T ⊗[R] S) d)
  let y := (awaySpectrumHomeomorph T d).symm x
  change Module.rankAtStalk (R := L)
    (Localization.Away (algebraMap T (T ⊗[R] S) d)) y = n
  rw [← congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) y]
  exact rankAtStalk_baseChange_of_isUnit R S g hetale n L
    (IsLocalization.Away.algebraMap_isUnit d) y

end SerrePositivity

end RankBaseChangePart
