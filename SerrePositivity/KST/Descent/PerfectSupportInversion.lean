module

public import SerrePositivity.KST.Descent.SupportAfterInversion
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality

/-!
# 閉台を持つ実際の有限射影複体の局所化での消滅

## 概要
イデアルの根基の元を単元にする底変換後、台つき有限射影複体が実際に零ホモトピー同値になる。

## 方針
実際の底変換の台の保存、閉台の空性、K-projective 性を順に適用する。

## 規約
可換な係数の既存の複体模型への適用である。非可換係数の T2・TT 局所化は別に残る。

## 使われ方
論文 (3.6) の Y = S, X での台の消滅の具体的な可換係数版。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {A B : Type u} [CommRing A] [CommRing B]

/-- 概要：根基の元が単元に写る底変換後の台つき有限射影複体は acyclic（論文 (3.6)）。
方針：実際の台の底変換の公式と閉台の消滅をホモロジーへ適用する。
規約：環の Noether 性・底変換の平坦性は不要。
使われ方：中心を逆にした後の支持圏の消滅の具体的な複体での検証。 -/
theorem supported_perfect_baseChange_acyclic (φ : A →+* B) (J : Ideal A) (p : A)
    (hp : p ∈ J.radical) (hunit : IsUnit (φ p))
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : strictlyPerfectComplex A P)
    (hs : HasHomologySupportOn (supportZeroLocus J) P) : (baseChange φ P).Acyclic := by
  have hb := hs.baseChange φ hP
  have hclosed : supportPullback φ (supportZeroLocus J) = ⊥ :=
    SetLike.coe_injective (support_preimage_empty_of_radical_isUnit φ J p hp hunit)
  rw [hclosed] at hb
  exact fun i ↦ (HomologicalComplex.exactAt_iff_isZero_homology _ i).mpr
    (hasHomologySupportOn_bot_iff.mp hb i)

/-- 概要：同じ底変換後の複体の恒等射は零へ実際にホモトピック（論文 (3.6)）。
方針：有限射影底変換の K-projective 性を前の acyclic 性と組み合わせる。
規約：ホモロジーの消滅だけで停止せず、実際のホモトピーを構成する。
使われ方：既存の perfect ホモトピー圏での零対象の判定。 -/
noncomputable def supported_perfect_baseChange_nullHomotopy (φ : A →+* B) (J : Ideal A) (p : A)
    (hp : p ∈ J.radical) (hunit : IsUnit (φ p))
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : strictlyPerfectComplex A P)
    (hs : HasHomologySupportOn (supportZeroLocus J) P) :
    Homotopy (𝟙 (baseChange φ P)) 0 := by
  have := strictlyPerfectComplex_isKProjective (strictlyPerfectComplex_baseChange φ P hP)
  exact CochainComplex.IsKProjective.homotopyZero _
    (supported_perfect_baseChange_acyclic φ J p hp hunit hP hs)

/-- 概要：底変換後の支持つき複体は実際のホモトピー圏で零対象（論文 (3.6)）。
方針：構成した零ホモトピーを商関手で写し、恒等射が零と等しいことを示す。
規約：K₀ 類だけの消滅より強い対象の消滅。
使われ方：TT 局所化の支持核との比較を供給する可換係数の幾何入力。 -/
theorem supported_perfect_baseChange_isZero (φ : A →+* B) (J : Ideal A) (p : A)
    (hp : p ∈ J.radical) (hunit : IsUnit (φ p))
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : strictlyPerfectComplex A P)
    (hs : HasHomologySupportOn (supportZeroLocus J) P) :
    IsZero ((homotopyQuot B).obj (baseChange φ P)) := by
  rw [IsZero.iff_id_eq_zero]
  have he := HomotopyCategory.eq_of_homotopy _ _
    (supported_perfect_baseChange_nullHomotopy φ J p hp hunit hP hs)
  exact ((homotopyQuot B).map_id _).symm.trans (he.trans ((homotopyQuot B).map_zero _ _))

end SerrePositivity.KST.Descent
