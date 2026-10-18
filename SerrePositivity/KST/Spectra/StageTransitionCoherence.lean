module

public import SerrePositivity.KST.Spectra.StageComparisonCoherence

/-!
概要：段の比較同型と隣接構造射の比較同型との整合性。
方針：前進比較の後続段の式を反復の定義と添字の等式から証明する。
規約：整数次数の計算次数が零となる段も含む。
使われ方：BF 1978 §2、HA §1.4.2。構造射による標準の安定群の段比較。
-/

@[expose] public section

universe u

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：添字の二回の移送は合成した等式による移送に一致する。
方針：四つの等式で帰納する。
規約：段と次数を同時に移送する。
使われ方：BF 1978 §2。隣接比較の添字の正規化。 -/
theorem levelHomotopyCongr_trans_apply (X : OmegaSpectrum.{u})
    {k l r n m s : ℕ} (hkl : k = l) (hlr : l = r) (hnm : n = m) (hms : m = s)
    (a : levelHomotopy X k n) :
    levelHomotopyCongr X hlr hms (levelHomotopyCongr X hkl hnm a) =
      levelHomotopyCongr X (hkl.trans hlr) (hnm.trans hms) a := by
  subst l
  subst r
  subst m
  subst s
  rfl

/-- 概要：隣接比較は段と次数の等式による移送と両立する。
方針：二つの等式で帰納する。
規約：標的の段と次数の等式には後続関数を適用する。
使われ方：BF 1978 §2。移送を隣接比較の後ろへ移す計算。 -/
theorem transition_congr_apply (X : OmegaSpectrum.{u}) {k l n m : ℕ}
    (hkl : k = l) (hnm : n = m) (a : levelHomotopy X k n) :
    transition X l m (levelHomotopyCongr X hkl hnm a) =
      levelHomotopyCongr X (congrArg Nat.succ hkl) (congrArg Nat.succ hnm)
        (transition X k n a) := by
  subst l
  subst m
  rfl

/-- 概要：前進比較を指定した反復回数で表示する。
方針：k+r=l から r=l-k を得て定義へ帰着する。
規約：等式の証明の選択には依存しない。
使われ方：BF 1978 §2。減算を含む添字を反復回数へ正規化する。 -/
theorem advanceTo_eq_iterate (X : OmegaSpectrum.{u}) (j : ℤ) (k l : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hkl : k ≤ l) (r : ℕ) (hr : k + r = l) :
    advanceTo X j k l hk hkl = (iterateTransition X k (degree j k) r).trans
      (levelHomotopyCongr X hr ((degree_add j k r hk).symm.trans (congrArg (degree j) hr))) := by
  have hr' : r = l - k := by omega
  subst r
  rfl

/-- 概要：同じ段への前進比較は恒等同型。
方針：反復回数が零であることと添字の反射律を使う。
規約：許される任意の段。
使われ方：BF 1978 §2。構造射による比較の開始点。 -/
@[simp]
theorem advanceTo_self (X : OmegaSpectrum.{u}) (j : ℤ) (k : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) : advanceTo X j k k hk (Nat.le_refl k) = MulEquiv.refl _ := by
  rw [advanceTo_eq_iterate X j k k hk (Nat.le_refl k) 0 rfl]
  rfl

/-- 概要：前進比較を一段延ばすと隣接段の比較との合成になる。
方針：k≤l を l=k+r と書き、反復の後続式と次数の加法を計算する。
規約：最後の次数の表示だけを等式で移送する。
使われ方：BF 1978 §2、HA §1.4.2。段の比較と構造射の整合性。 -/
theorem advanceTo_succ (X : OmegaSpectrum.{u}) (j : ℤ) (k l : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hkl : k ≤ l) :
    (advanceTo X j k l hk hkl).trans
      ((transition X l (degree j l)).trans
        (levelHomotopyCongr X rfl (degree_add j l 1 (by omega)).symm)) =
      advanceTo X j k (l + 1) hk (by omega) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [advanceTo_eq_iterate X j k (k + r) hk hkl r rfl,
    advanceTo_eq_iterate X j k (k + r + 1) hk (by omega) (r + 1) rfl]
  ext a
  simp only [MulEquiv.trans_apply, iterateTransition]
  rw [transition_congr_apply, levelHomotopyCongr_trans_apply]
  rfl

/-- 概要：隣接する二段の比較は構造射による隣接比較に一致する。
方針：最小段からの後続式を使い、それ以前の比較の往復を打ち消す。
規約：最後に実際の計算次数の表示を移送する。
使われ方：BF 1978 §2、HA §1.4.2。安定群の段比較と構造射の一致。 -/
theorem compareLevels_succ (X : OmegaSpectrum.{u}) (j : ℤ) (k : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) :
    compareLevels X j k (k + 1) hk (by omega) =
      (transition X k (degree j k)).trans
        (levelHomotopyCongr X rfl (degree_add j k 1 hk).symm) := by
  rw [compareLevels, ← advanceTo_succ X j (initialLevel j) k
    (initialLevel_admissible j) (initialLevel_le j k hk)]
  ext a
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- 概要：より高い段への前進比較は二段比較と一致する。
方針：終点の段に関する帰納で隣接比較の式と三段の合成法則を使う。
規約：k≤l を要求する。
使われ方：BF 1978 §2、HA §1.4.2。反復構造射による標準表示。 -/
theorem advanceTo_eq_compareLevels (X : OmegaSpectrum.{u}) (j : ℤ) (k l : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hkl : k ≤ l) :
    advanceTo X j k l hk hkl = compareLevels X j k l hk (by omega) := by
  induction l, hkl using Nat.le_induction with
  | base => rw [advanceTo_self, compareLevels_refl]
  | succ l hkl ih =>
    have hl : 0 ≤ j + (l : ℤ) := by omega
    rw [← advanceTo_succ X j k l hk hkl, ih, ← compareLevels_succ X j l hl,
      compareLevels_trans]

/-- 概要：構造射の反復は次数を整えると任意段の比較と一致する。
方針：指定した反復回数による前進表示と二段比較との一致を合成する。
規約：最初の計算次数は degree j k。
使われ方：BF 1978 §2、HA §1.4.2。π_j(X)=π_(j+k)(X_k) の構造射に関する整合性。 -/
theorem iterateTransition_eq_compareLevels (X : OmegaSpectrum.{u}) (j : ℤ) (k r : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) :
    (iterateTransition X k (degree j k) r).trans
      (levelHomotopyCongr X rfl (degree_add j k r hk).symm) =
        compareLevels X j k (k + r) hk (by omega) :=
  (advanceTo_eq_iterate X j k (k + r) hk (by omega) r rfl).symm.trans
    (advanceTo_eq_compareLevels X j k (k + r) hk (by omega))

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
