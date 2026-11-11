module

public import SerrePositivity.KST.Spectra.OmegaSpectrumZeroGroups

/-!
概要：Ω スペクトルの整数次数の可換ホモトピー群と段の選択の比較。
方針：隣接段の同型を反復し、最小の許される段からの同型で各段を比較する。
規約：定義の標準段は |j|+1、任意の k≥−j で π_(j+k)(X_k) と群同型。
使われ方：BF 1978 §2、HA §1.4.2。KST の全次数 π_* 同型。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Ω スペクトルの指定段の実際の自然数次数の群。
方針：零次数も可換群にした KanHomotopy を用いる。
規約：k はスペクトルの段、n は実際の次数。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の段による表示。 -/
abbrev levelHomotopy (X : OmegaSpectrum.{u}) (k n : ℕ) : Type u :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (X.level k).space.right n (X.level k).space.basepoint

/-- 概要：整数次数 j の標準の計算段。
方針：|j|+1 を選ぶことで計算する次数を正にする。
規約：任意の他の許される段と比較する。
使われ方：BF 1978 §2。整数次数の群の定義。 -/
def canonicalLevel (j : ℤ) : ℕ := j.natAbs + 1

/-- 概要：整数次数 j を段 k で計算する自然数次数。
方針：j+k の自然数への変換を取る。
規約：比較同型では j+k≥0 を条件として明示する。
使われ方：BF 1978 §2、HA §1.4.2。安定ホモトピー群の添字。 -/
def degree (j : ℤ) (k : ℕ) : ℕ := (j + (k : ℤ)).toNat

/-- 概要：標準段での計算次数は非負。
方針：整数の符号で場合分けして計算する。
規約：標準段は |j|+1。
使われ方：BF 1978 §2。段の比較の適用条件。 -/
theorem canonicalLevel_admissible (j : ℤ) : 0 ≤ j + (canonicalLevel j : ℤ) := by
  cases j <;> simp [canonicalLevel] <;> omega

/-- 概要：標準段での計算次数は正。
方針：整数の符号で場合分けして計算する。
規約：後続の射への作用を正次数の誘導準同型で定義するための条件。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の関手性。 -/
theorem canonicalDegree_pos (j : ℤ) : 0 < degree j (canonicalLevel j) := by
  cases j <;> simp [canonicalLevel, degree] <;> omega

/-- 概要：許される段を r 上げると計算する次数も r 上がる。
方針：非負な整数の自然数変換の算術を使う。
規約：j+k≥0 を明示する。
使われ方：BF 1978 §2。段の反復比較の添字。 -/
theorem degree_add (j : ℤ) (k r : ℕ) (hk : 0 ≤ j + (k : ℤ)) :
    degree j (k + r) = degree j k + r := by
  unfold degree
  omega

/-- 概要：段と次数の等式による群の同型。
方針：二つの等式で帰納する。
規約：スペクトル X は固定する。
使われ方：BF 1978 §2。反復した段の比較の添字を整える。 -/
def levelHomotopyCongr (X : OmegaSpectrum.{u}) {k l n m : ℕ} (hkl : k = l) (hnm : n = m) :
    levelHomotopy X k n ≃* levelHomotopy X l m := by
  subst l
  subst m
  exact MulEquiv.refl _

/-- 概要：隣接段の群同型を r 回反復する。
方針：構造射と loop の次数移動の同型を順に合成する。
規約：段と次数を同時に r 上げる。
使われ方：BF 1978 §2、HA §1.4.2。安定群の段の選択独立性。 -/
def iterateTransition (X : OmegaSpectrum.{u}) (k n : ℕ) :
    (r : ℕ) → (levelHomotopy X k n ≃* levelHomotopy X (k + r) (n + r))
  | 0 => MulEquiv.refl _
  | r + 1 => (iterateTransition X k n r).trans (transition X (k + r) (n + r))

/-- 概要：許される計算段 k からより高い段 l への群同型。
方針：隣接段の同型を l-k 回反復し、添字を等式で整える。
規約：k≤l と j+k≥0 を明示する。
使われ方：BF 1978 §2。共通の高い段への比較。 -/
def advanceTo (X : OmegaSpectrum.{u}) (j : ℤ) (k l : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hkl : k ≤ l) :
    levelHomotopy X k (degree j k) ≃* levelHomotopy X l (degree j l) := by
  have hl : k + (l - k) = l := Nat.add_sub_of_le hkl
  have hd : degree j k + (l - k) = degree j l := by rw [← degree_add j k (l - k) hk, hl]
  exact (iterateTransition X k (degree j k) (l - k)).trans (levelHomotopyCongr X hl hd)

/-- 概要：整数次数の最小の許される計算段。
方針：−j の非負部分を取る。
規約：標準の計算段 |j|+1 とは区別する。
使われ方：BF 1978 §2。全ての段の比較の合成整合性。 -/
def initialLevel (j : ℤ) : ℕ := (-j).toNat

/-- 概要：最小段での計算次数は非負。
方針：整数の自然数変換の算術を使う。
規約：j が非負なら零段を使う。
使われ方：BF 1978 §2。最小段からの前進同型。 -/
theorem initialLevel_admissible (j : ℤ) : 0 ≤ j + (initialLevel j : ℤ) := by
  unfold initialLevel
  omega

/-- 概要：許される段は最小段以上である。
方針：非負な計算次数から整数の不等式を得る。
規約：全て自然数の段を比較する。
使われ方：BF 1978 §2。共通の源を持つ比較同型。 -/
theorem initialLevel_le (j : ℤ) (k : ℕ) (hk : 0 ≤ j + (k : ℤ)) : initialLevel j ≤ k := by
  unfold initialLevel
  omega

/-- 概要：整数次数を任意の二つの許される段で計算した群の比較。
方針：最小の許される段から各段への前進同型を通じて比較する。
規約：零次数の計算段も含む。
使われ方：BF 1978 §2、HA §1.4.2。段によらない安定ホモトピー群。 -/
def compareLevels (X : OmegaSpectrum.{u}) (j : ℤ) (k l : ℕ)
    (hk : 0 ≤ j + (k : ℤ)) (hl : 0 ≤ j + (l : ℤ)) :
    levelHomotopy X k (degree j k) ≃* levelHomotopy X l (degree j l) :=
  (advanceTo X j (initialLevel j) k (initialLevel_admissible j) (initialLevel_le j k hk)).symm.trans
    (advanceTo X j (initialLevel j) l (initialLevel_admissible j) (initialLevel_le j l hl))

/-- 概要：Ω スペクトルの整数次数のホモトピー群。
方針：標準段 |j|+1 の π_(j+|j|+1) を取る。
規約：任意の k≥−j の段による表示との群同型を別途与える。
使われ方：BF 1978 §2、HA §1.4.2。KST の π_* 同型。 -/
def homotopyGroup (X : OmegaSpectrum.{u}) (j : ℤ) : Type u :=
  levelHomotopy X (canonicalLevel j) (degree j (canonicalLevel j))

/-- 概要：整数次数のホモトピー群は可換群。
方針：構成済みの各段の可換群構造を使う。
規約：加法化は必要な利用側で行う。
使われ方：BF 1978 §2、HA §1.4.2。有理化と完全列。 -/
instance homotopyGroupCommGroup (X : OmegaSpectrum.{u}) (j : ℤ) : CommGroup (homotopyGroup X j) :=
  inferInstanceAs (CommGroup (levelHomotopy X (canonicalLevel j) (degree j (canonicalLevel j))))

/-- 概要：整数次数の群を任意の許される段の群で計算する同型。
方針：標準段と指定段を最小段からの前進同型を通じて比較する。
規約：k≥−j の条件を整数の不等式で明示する。
使われ方：BF 1978 §2、HA §1.4.2。π_j(X)=π_(j+k)(X_k) の段の独立性。 -/
def homotopyGroupEquivAt (X : OmegaSpectrum.{u}) (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) :
    homotopyGroup X j ≃* levelHomotopy X k (degree j k) :=
  compareLevels X j (canonicalLevel j) k (canonicalLevel_admissible j) (by omega)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
