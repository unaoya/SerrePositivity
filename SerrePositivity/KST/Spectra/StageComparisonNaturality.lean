module

public import SerrePositivity.KST.Spectra.SpectrumLevelFunctor
public import SerrePositivity.KST.Spectra.StageComparisonCoherence

/-!
概要：整数次数の任意段表示の自然性。
方針：隣接段の自然性を反復し、添字の移送と逆同型へ延ばす。
規約：零次数となる段も含む可換群の自然同型を与える。
使われ方：BF 1978 §2、HA §1.4.2。π_* 同型を任意の十分高い段で検証する界面。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：整数次数の誘導準同型は標準段の全次数の誘導準同型と同じ。
方針：正次数の計算式を同じホモトピー類の写像へ直す。
規約：標準段の計算次数は正。
使われ方：BF 1978 §2。整数次数の関手と段の関手の比較。 -/
theorem homotopyMap_eq_levelMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) :
    homotopyMap f j = levelMap f (canonicalLevel j) (degree j (canonicalLevel j)) := by
  apply MonoidHom.ext
  intro a
  rw [homotopyMap_apply]
  rfl

/-- 概要：隣接段の比較の反復は射に関して自然。
方針：反復回数に関する帰納と隣接比較の自然性を使う。
規約：段と次数を同時に r 上げる。
使われ方：BF 1978 §2。任意段の自然な比較。 -/
theorem iterateTransition_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (k n r : ℕ)
    (a : levelHomotopy X k n) :
    iterateTransition Y k n r (levelMap f k n a) =
      levelMap f (k + r) (n + r) (iterateTransition X k n r a) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [iterateTransition, MulEquiv.trans_apply]
    rw [ih]
    exact transition_natural f (k + r) (n + r) _

/-- 概要：段と次数の等式による移送は誘導準同型と可換。
方針：二つの等式で帰納する。
規約：スペクトルの射を固定する。
使われ方：BF 1978 §2。比較同型の添字の正規化。 -/
theorem levelHomotopyCongr_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    {k l n m : ℕ} (hkl : k = l) (hnm : n = m) (a : levelHomotopy X k n) :
    levelHomotopyCongr Y hkl hnm (levelMap f k n a) =
      levelMap f l m (levelHomotopyCongr X hkl hnm a) := by
  subst l
  subst m
  rfl

/-- 概要：より高い許される段への比較は射に関して自然。
方針：反復比較と添字の等式の自然性を合成する。
規約：整数次数 j と k≤l を固定する。
使われ方：BF 1978 §2。最小段からの自然な前進。 -/
theorem advanceTo_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) (k l : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hkl : k ≤ l) (a : levelHomotopy X k (degree j k)) :
    advanceTo Y j k l hk hkl (levelMap f k (degree j k) a) =
      levelMap f l (degree j l) (advanceTo X j k l hk hkl a) := by
  dsimp only [advanceTo, MulEquiv.trans_apply]
  rw [iterateTransition_natural]
  exact levelHomotopyCongr_natural f _ _ _

/-- 概要：高い段から戻る逆比較も射に関して自然。
方針：順比較の単射性と自然性を使う。
規約：逆向きの表示に新しい選択を入れない。
使われ方：BF 1978 §2。任意の二段の自然な比較。 -/
theorem advanceTo_symm_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) (k l : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hkl : k ≤ l) (a : levelHomotopy X l (degree j l)) :
    (advanceTo Y j k l hk hkl).symm (levelMap f l (degree j l) a) =
      levelMap f k (degree j k) ((advanceTo X j k l hk hkl).symm a) := by
  apply (advanceTo Y j k l hk hkl).injective
  rw [MulEquiv.apply_symm_apply, advanceTo_natural, MulEquiv.apply_symm_apply]

/-- 概要：任意の二つの許される段の比較はスペクトルの射に関して自然。
方針：最小段からの順比較と逆比較の自然性を合成する。
規約：段の大小関係を要求しない。
使われ方：BF 1978 §2、HA §1.4.2。安定ホモトピー群の自然な段の独立性。 -/
theorem compareLevels_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) (k l : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hl : 0 ≤ j + (l : ℤ))
    (a : levelHomotopy X k (degree j k)) :
    compareLevels Y j k l hk hl (levelMap f k (degree j k) a) =
      levelMap f l (degree j l) (compareLevels X j k l hk hl a) := by
  simp only [compareLevels, MulEquiv.trans_apply]
  rw [advanceTo_symm_natural, advanceTo_natural]

/-- 概要：整数次数群の任意段での表示はスペクトルの射に関して自然。
方針：標準段の写像を段の写像に直し、二段比較の自然性を使う。
規約：k≥−j の全ての段で有効。
使われ方：BF 1978 §2、HA §1.4.2。π_* 同型の段ごとの検証。 -/
theorem homotopyGroupEquivAt_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) (a : homotopyGroup X j) :
    homotopyGroupEquivAt Y j k hk (homotopyMap f j a) =
      levelMap f k (degree j k) (homotopyGroupEquivAt X j k hk a) := by
  rw [homotopyMap_eq_levelMap]
  exact compareLevels_natural f j (canonicalLevel j) k _ _ a

/-- 概要：整数次数群の関手は任意の許される段の群の関手と自然同型。
方針：各対象の群同型と証明済みの自然性を束ねる。
規約：可換群の通常の圏での自然同型。
使われ方：BF 1978 §2、HA §1.4.2。任意段を使う完全列と有理化の計算。 -/
def homotopyFunctorIsoAt (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) :
    homotopyFunctor j ≅ levelFunctor k (degree j k) :=
  NatIso.ofComponents (fun X ↦ (homotopyGroupEquivAt X j k hk).toCommGrpIso) (fun f ↦ by
    ext a
    exact homotopyGroupEquivAt_natural f j k hk a)

/-- 概要：整数次数の誘導写像の全単射性は任意の許される段で検証できる。
方針：自然な比較同型を前後に合成して全単射性を移す。
規約：k≥−j のみを要求し、零次数となる段も許す。
使われ方：BF 1978 §2、HA §1.4.2。定理 3.1 の π_* 同型の段ごとの検証。 -/
theorem homotopyMap_bijective_iff_levelMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) :
    Function.Bijective (homotopyMap f j) ↔ Function.Bijective (levelMap f k (degree j k)) := by
  let eX := homotopyGroupEquivAt X j k hk
  let eY := homotopyGroupEquivAt Y j k hk
  have h : eY ∘ homotopyMap f j = levelMap f k (degree j k) ∘ eX := by
    funext a
    exact homotopyGroupEquivAt_natural f j k hk a
  calc
    Function.Bijective (homotopyMap f j) ↔ Function.Bijective (eY ∘ homotopyMap f j) :=
      (Function.Bijective.of_comp_iff' eY.bijective _).symm
    _ ↔ Function.Bijective (levelMap f k (degree j k) ∘ eX) := by rw [h]
    _ ↔ Function.Bijective (levelMap f k (degree j k)) :=
      Function.Bijective.of_comp_iff _ eX.bijective

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
