module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyGroups

/-!
概要：整数次数のホモトピー群の段による比較同型の合成整合性。
方針：共通の最小段からの同型と逆同型を打ち消す。
規約：零次数となる計算段も含む。
使われ方：BF 1978 §2、HA §1.4.2。安定群の段の選択独立性。
-/

@[expose] public section

universe u

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

/-- 概要：同じ段同士の比較は恒等同型。
方針：最小段からの同型とその逆を打ち消す。
規約：許される任意の段。
使われ方：BF 1978 §2。段の比較の単位法則。 -/
@[simp]
theorem compareLevels_refl (X : OmegaSpectrum.{u}) (j : ℤ) (k : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) : compareLevels X j k k hk hk = MulEquiv.refl _ := by
  ext a
  simp [compareLevels]

/-- 概要：二段の逆向きの比較は順向きの逆同型。
方針：二つの最小段からの同型の合成順序を反転する。
規約：両段の非負次数条件を明示する。
使われ方：BF 1978 §2。段の比較の逆法則。 -/
theorem compareLevels_symm (X : OmegaSpectrum.{u}) (j : ℤ) (k l : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hl : 0 ≤ j + (l : ℤ)) :
    (compareLevels X j k l hk hl).symm = compareLevels X j l k hl hk := by
  ext a
  rfl

/-- 概要：三段の比較の合成は直接の比較と一致する。
方針：中間段と最小段の往復を打ち消す。
規約：全ての許される段を任意の順序で比較する。
使われ方：BF 1978 §2、HA §1.4.2。段の選択の合成整合性。 -/
theorem compareLevels_trans (X : OmegaSpectrum.{u}) (j : ℤ) (k l m : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hl : 0 ≤ j + (l : ℤ)) (hm : 0 ≤ j + (m : ℤ)) :
    (compareLevels X j k l hk hl).trans (compareLevels X j l m hl hm) =
      compareLevels X j k m hk hm := by
  ext a
  simp [compareLevels]

/-- 概要：標準段による群の、標準段そのものへの比較は恒等同型。
方針：同じ段同士の比較の単位法則を使う。
規約：定義の標準段は |j|+1。
使われ方：BF 1978 §2。整数次数の群の標準表示。 -/
@[simp]
theorem homotopyGroupEquivAt_canonical (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroupEquivAt X j (canonicalLevel j) (by
      have h := canonicalLevel_admissible j
      omega) = MulEquiv.refl (homotopyGroup X j) :=
  compareLevels_refl X j _ _

/-- 概要：整数次数の群から段 k への表示を段 l へ移すと直接の段 l 表示になる。
方針：段の比較の合成整合性を標準段から適用する。
規約：k と l は任意の許される段。
使われ方：BF 1978 §2、HA §1.4.2。任意段での計算の整合性。 -/
theorem homotopyGroupEquivAt_trans (X : OmegaSpectrum.{u}) (j : ℤ) (k l : ℕ)
    (hk : -j ≤ (k : ℤ)) (hl : -j ≤ (l : ℤ)) :
    (homotopyGroupEquivAt X j k hk).trans
      (compareLevels X j k l (by omega) (by omega)) = homotopyGroupEquivAt X j l hl :=
  compareLevels_trans X j _ k l _ _ _

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
