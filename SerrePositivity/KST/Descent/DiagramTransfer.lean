module

public import SerrePositivity.KST.Descent.PiComparison
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Tactic.NormNum

/-!
# 補題 3.2 の図式上の transfer と比較写像の retract

## 概要
rank の局所公式を満たす自然変換から、前層そのものの retract を作る。
自然な比較射に任意の二つの関手を適用して、比較射の retract を得る。

## 方針
有理線形な値域で自然変換を rank の逆数倍にし、自然性から矢の圏の retract を構成する。

## 規約
有限平坦 transfer の存在・射影公式の検証は別に必要。
二つの関手を次数ごとの通常の極限と解釈しない。
Tot を使うときは、外部で構成した実際の図式関手と比較自然変換を入力する。

## 使われ方
論文 補題 3.2 の「降下比較は分裂降下比較の retract」という部分。
τ 位相の層論を Čech 計算へ置き換える際の関手的な機構。
-/

@[expose] public section

open CategoryTheory CategoryTheory.Linear

namespace SerrePositivity.KST.Descent

section Transfer

variable {D : Type*} [Category* D] [Preadditive D] [Linear ℚ D]

/-- 概要：有理線形な図式の圏で rank 公式から retract を得る（論文 補題 3.2）。
方針：transfer の rank の逆数倍を retraction とする。
規約：D は導来図式を保持する圏でもよく、次数ごとの群の圏に限定しない。
使われ方：実際の homotopy limit の関手が作用する図式の分裂を作る。 -/
def rankTransferRetract {F G : D} (rank : ℕ) (positive : 0 < rank)
    (pullback : F ⟶ G) (transfer : G ⟶ F)
    (rank_identity : pullback ≫ transfer = (rank : ℚ) • 𝟙 F) : Retract F G where
  i := pullback
  r := (rank : ℚ)⁻¹ • transfer
  retract := by
    rw [comp_smul, rank_identity, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast positive.ne'), one_smul]

end Transfer

section NaturalTransfer

variable {J V : Type*} [Category* J] [Category* V] [Preadditive V] [Linear ℚ V]

/-- 概要：自然変換としての transfer の正規化（論文 補題 3.2）。
方針：関手圏の有理線形構造で rank の逆数倍を取る。
規約：rank はベクトル束を自明化した開集合上で一つに固定する。
使われ方：全 Čech 図式に共通する自然な retraction。 -/
def normalizedNaturalTransfer {F G : J ⥤ V} (rank : ℕ) (transfer : G ⟶ F) : G ⟶ F :=
  (rank : ℚ)⁻¹ • transfer

/-- 概要：rank 公式から前層そのものの retract を構成する（論文 補題 3.2）。
方針：正の rank を有理線形な関手圏で消去する。
規約：rank 公式は自然変換の等式であり、対象ごとの同型の選択ではない。
使われ方：Tot などの図式関手を適用して比較射の retract を作る。 -/
def naturalTransferRetract {F G : J ⥤ V} (rank : ℕ) (positive : 0 < rank)
    (pullback : F ⟶ G) (transfer : G ⟶ F)
    (rank_identity : pullback ≫ transfer = (rank : ℚ) • 𝟙 F) : Retract F G :=
  rankTransferRetract rank positive pullback transfer rank_identity

end NaturalTransfer

section Comparison

variable {D V : Type*} [Category* D] [Category* V]

/-- 概要：自然な比較に二つの関手を適用すると矢の圏の retract が得られる（補題 3.2）。
方針：自然性の二つの正方形と、関手が保存する分裂恒等式を使う。
規約：source と target は同じ実際の導来図式に対する二つの関手。
使われ方：augmentation の値と Čech Tot の比較に適用する。 -/
def naturalComparisonRetract (source target : D ⥤ V) (comparison : source ⟶ target)
    {F G : D} (h : Retract F G) :
    RetractArrow (comparison.app F) (comparison.app G) where
  i := Arrow.homMk (source.map h.i) (target.map h.i) (comparison.naturality h.i)
  r := Arrow.homMk (source.map h.r) (target.map h.r) (comparison.naturality h.r)
  retract := by
    ext <;> simp [← source.map_comp, ← target.map_comp, h.retract]

/-- 概要：自然な比較の全次数同型は元の図式の retract に引き継がれる（補題 3.2）。
方針：比較射の retract を作り、全次数同型の retract 安定性を適用する。
規約：観測関手が L9 の π_n に接続されれば、これが全次数の降下移行になる。
使われ方：有限平坦 transfer による補題 3.2 の局所的な retract 論法。 -/
theorem piComparison_of_retract (observation : ℤ → V ⥤ ModuleCat ℚ)
    (source target : D ⥤ V) (comparison : source ⟶ target)
    {F G : D} (h : Retract F G)
    (hG : piIsomorphisms observation (comparison.app G)) :
    piIsomorphisms observation (comparison.app F) :=
  piIsomorphisms_of_retract observation (naturalComparisonRetract source target comparison h) hG

/-- 概要：rank 公式と分裂側の降下から元の比較の全次数同型を得る（論文 補題 3.2）。
方針：図式上の transfer を正規化し、比較射の retract に移して全次数同型を保存する。
規約：D の射は導来図式の射を保持し、比較自然変換もその図式上で与える。
使われ方：有限平坦射の局所自明化後の、補題 3.2 の transfer による降下移行。 -/
theorem piComparison_of_transfer [Preadditive D] [Linear ℚ D]
    (observation : ℤ → V ⥤ ModuleCat ℚ)
    (source target : D ⥤ V) (comparison : source ⟶ target)
    {F G : D} (rank : ℕ) (positive : 0 < rank)
    (pullback : F ⟶ G) (transfer : G ⟶ F)
    (rank_identity : pullback ≫ transfer = (rank : ℚ) • 𝟙 F)
    (hG : piIsomorphisms observation (comparison.app G)) :
    piIsomorphisms observation (comparison.app F) :=
  piComparison_of_retract observation source target comparison
    (rankTransferRetract rank positive pullback transfer rank_identity) hG

end Comparison

end SerrePositivity.KST.Descent
