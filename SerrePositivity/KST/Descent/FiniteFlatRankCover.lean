module

public import SerrePositivity.KST.Descent.FiniteTypeLimits
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# 有限忠実平坦射の正の定 rank の有限開被覆

## 概要
実際の有限平坦有限表示射の rank により基底を分け、正の定 rank の被覆を構成する。

## 方針
Mathlib の rank の局所定数性と底変換公式を使い、準コンパクト性から値域の有限性を得る。

## 規約
基底全体で同じ rank とは仮定しない。空の基底では添字型も空になりうる。

## 使われ方
論文 補題 3.2 の transfer の正規化と、補題 3.3 の平坦化後の実際の被覆。
原典の τ 位相の層論を Čech 計算で置換する際の Zariski 還元の幾何入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
  [LocallyOfFinitePresentation f]

/-- 概要：有限平坦射の実際の rank が n である開部分（論文 補題 3.2）。
方針：rank の局所定数性を一元集合の逆像に適用する。
規約：空の層も許す。開部分は実際の基底上に取る。
使われ方：局所 rank 公式を一つの正の整数倍にする。 -/
noncomputable def finiteFlatRankOpen (n : ℕ) : Y.Opens :=
  ⟨f.finrank ⁻¹' {n}, f.isLocallyConstant_finrank {n}⟩

/-- 概要：実際に現れる rank の添字型（論文 補題 3.2）。
方針：rank 関数の値域を取る。
規約：全自然数を被覆の添字にせず、空の層を除く。
使われ方：準コンパクトな基底上の有限な rank 被覆。 -/
abbrev FiniteFlatRankIndex := Set.range f.finrank

/-- 概要：準コンパクトな基底では rank の値域は有限（論文 補題 3.2）。
方針：局所定数関数のコンパクト像の有限性を使う。
規約：rank の全域一様性は要求しない。
使われ方：実際の有限開被覆への有限性の供給。 -/
instance [CompactSpace Y] : Finite (FiniteFlatRankIndex f) :=
  (f.isLocallyConstant_finrank.range_finite).to_subtype

/-- 概要：rank の層による実際の基底の開被覆（論文 補題 3.2）。
方針：各点をその rank の層で覆う。
規約：各射は元の基底の開包含そのもの。
使われ方：実際の Čech の Zariski 降下へ供給する幾何被覆。 -/
noncomputable def finiteFlatRankOpenCover : Y.OpenCover where
  I₀ := FiniteFlatRankIndex f
  X n := finiteFlatRankOpen f n.val
  f n := (finiteFlatRankOpen f n.val).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro y
    exact ⟨⟨f.finrank y, ⟨y, rfl⟩⟩, ⟨⟨y, rfl⟩, rfl⟩⟩

/-- 概要：rank 被覆の添字は準コンパクト基底上で有限（論文 補題 3.2）。
方針：rank 値域の有限性をそのまま使う。
規約：実際の開被覆の添字型についての主張。
使われ方：有限個の開部分での transfer 正規化と Zariski 貼り合わせ。 -/
instance [CompactSpace Y] : Finite (finiteFlatRankOpenCover f).I₀ :=
  inferInstanceAs (Finite (FiniteFlatRankIndex f))

omit [LocallyOfFinitePresentation f] in
/-- 概要：忠実平坦な有限射の各非空 rank 層の rank は正（論文 補題 3.2）。
方針：層の点を選び、全射性と rank の正値判定を使う。
規約：正値性を別の幾何公理として仮定しない。
使われ方：有理係数で rank の逆数を使う正規化。 -/
theorem finiteFlatRankIndex_positive [Surjective f] (n : FiniteFlatRankIndex f) :
    0 < n.val := by
  obtain ⟨y, hy⟩ := n.property
  have h := (f.one_le_finrank_iff_surjective.mpr inferInstance) y
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (hy ▸ h)

/-- 概要：各 rank 開部分への実際の底変換射は指定した定 rank（論文 補題 3.2）。
方針：有限平坦射の底変換 rank 公式と開部分の所属条件を使う。
規約：基底全体での定 rank は要求しない。
使われ方：局所 rank 公式を定数の整数倍として transfer へ供給する。 -/
theorem finiteFlatRankOpen_pullback_rank (n : ℕ) (y : finiteFlatRankOpen f n) :
    (pullback.snd f (finiteFlatRankOpen f n).ι).finrank y = n :=
  (Scheme.Hom.finrank_pullback_snd f (finiteFlatRankOpen f n).ι y).trans
    (show f.finrank y.val = n from y.property)

/-- 概要：rank 開部分上の定 rank はさらに任意の底変換で保たれる（論文 補題 3.2）。
方針：二段の底変換の rank 公式を合成する。
規約：Čech の各段にも適用でき、観測 π_* と Tot の交換を使わない。
使われ方：同じ正の rank による各 Čech 段の transfer 正規化。 -/
theorem finiteFlatRankOpen_baseChange_rank (n : ℕ) {T : Scheme.{u}}
    (g : T ⟶ finiteFlatRankOpen f n) (t : T) :
    (pullback.snd (pullback.snd f (finiteFlatRankOpen f n).ι) g).finrank t = n :=
  (Scheme.Hom.finrank_pullback_snd _ g t).trans (finiteFlatRankOpen_pullback_rank f n (g t))

section FiniteType

variable {S : Scheme.{u}} [IsNoetherian S]

/-- 概要：Noether 基底上の有限型対象の開部分を同じ有限型の圏へ持ち上げる（論文 補題 3.2）。
方針：開包含の局所有限型性と Noether 性による準コンパクト性を合成する。
規約：任意のスキーム上の開包含が準コンパクトとは仮定しない。
使われ方：rank 開被覆の各対象を元の前層 L の定義域に置く。 -/
noncomputable def finiteTypeOpen (Y : FiniteTypeSchemes S) (U : Y.obj.left.Opens) :
    FiniteTypeSchemes S := by
  have : LocallyOfFiniteType Y.obj.hom := Y.property.1
  have : QuasiCompact Y.obj.hom := Y.property.2
  exact ⟨Over.mk (U.ι ≫ Y.obj.hom), locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：元の有限型の圏内の開包含（論文 補題 3.2）。
方針：実際の開包含を同じ基底上の射にする。
規約：underlying scheme の射は U.ι。
使われ方：同じ前層による rank 開部分への制限。 -/
noncomputable def finiteTypeOpenInclusion (Y : FiniteTypeSchemes S) (U : Y.obj.left.Opens) :
    finiteTypeOpen Y U ⟶ Y := ObjectProperty.homMk (Over.homMk U.ι)

variable {A B : FiniteTypeSchemes S} (p : A ⟶ B)
  [IsFinite p.hom.left] [Flat p.hom.left] [LocallyOfFinitePresentation p.hom.left]

/-- 概要：rank 開部分への底変換は元の有限型の圏内で同じ定 rank（論文 補題 3.2）。
方針：指定された引き戻しの underlying scheme の公式へ実際の rank 公式を適用する。
規約：前層の定義域と指定射を交換しない。
使われ方：平坦化後の有限忠実平坦細分と元の transfer 界面の接続。 -/
theorem finiteTypeRankOpen_pullback_rank (n : ℕ)
    (y : (finiteTypeOpen B (finiteFlatRankOpen p.hom.left n)).obj.left) :
    (finiteTypePullbackSnd p
      (finiteTypeOpenInclusion B (finiteFlatRankOpen p.hom.left n))).hom.left.finrank y = n :=
  finiteFlatRankOpen_pullback_rank p.hom.left n y

end FiniteType

end SerrePositivity.KST.Descent
