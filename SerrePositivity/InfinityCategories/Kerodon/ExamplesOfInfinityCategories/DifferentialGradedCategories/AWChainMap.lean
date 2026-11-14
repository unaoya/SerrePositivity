module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWBoundaryTerms
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.KSTProExcisionAWBoundaryExpansion
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.KSTProExcisionAWBoundarySum
public import Mathlib.Tactic.CrossRefAttribute

/-!
# AW の境界和の合成

概要：実境界の展開、非対角の添字変換、対角の相殺を同じ切断の座標にまとめる。
方針：水平・垂直・削除後の切断・対角の項を定義し、区間の公式を適用する。
規約：KST Construction A.5 の標準 AW。前半と後半は切断点を共有する。
使われ方：Alexander–Whitney の成分を実際の鎖写像へ束ねる。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：切断点 i の水平境界の面 k に対応する項。
方針：長さ i+1 の前半の面を取り、後半を固定する。
規約：KST A.5、符号を付ける前の写像。使われ方：水平境界の有限和。 -/
def awHorizontalFaceTerm (n : ℕ) (i : Fin (n + 1)) (k : Fin ((i : ℕ) + 2)) :=
  awTensorTerm C D
    (SimplexCategory.δ k ≫ awInterval 0 ((i : ℕ) + 1) (n + 1) (by have := i.isLt; omega))
    (awInterval ((i : ℕ) + 1) (n - (i : ℕ)) (n + 1) (by have := i.isLt; omega)) (awDegrees n i)

/-- 概要：切断点 i の垂直境界の面 k に対応する項。
方針：前半を固定し、長さ n−i+1 の後半の面を取る。
規約：KST A.5、垂直微分の外側の符号は含めない。使われ方：垂直境界の有限和。 -/
def awVerticalFaceTerm (n : ℕ) (i : Fin (n + 1)) (k : Fin (n - (i : ℕ) + 2)) :=
  awTensorTerm C D (awInterval 0 i (n + 1) (by have := i.isLt; omega))
    (SimplexCategory.δ k ≫ awInterval i (n - (i : ℕ) + 1) (n + 1)
      (by have := i.isLt; omega)) (awDegrees n i)

/-- 概要：全単体の頂点 k を削除し、その後に i で切断した項。
方針：二つの切断の制限に同じ面を後合成する。
規約：KST A.5、削除点の符号は含めない。使われ方：source の境界和。 -/
def awDeletedFaceTerm (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)) :=
  awTensorTerm C D (awFront n i ≫ SimplexCategory.δ k)
    (awBack n i ≫ SimplexCategory.δ k) (awDegrees n i)

/-- 概要：隣接する二つの切断点から現れる共通の対角項。
方針：前半は i まで、後半は i+1 から取る。
規約：KST A.5、境界でのみ現れ、二つの因子に共有頂点はない。
使われ方：水平・垂直境界の相殺。 -/
def awCutDiagonalTerm (n : ℕ) (i : Fin (n + 1)) :=
  awTensorTerm C D (awInterval 0 i (n + 1) (by have := i.isLt; omega))
    (awInterval ((i : ℕ) + 1) (n - (i : ℕ)) (n + 1)
      (by have := i.isLt; omega)) (awDegrees n i)

/-- 概要：実水平境界の項を長さ n−i の共通の区間座標へ移す。
方針：前半・後半を区間と同定し、n+1−(i+1)=n−i を使う。
規約：KST A.5、制限項の長さの等式による同定。
使われ方：実水平境界の展開への有限和の適用。 -/
lemma awHorizontalFaceTerm_eq (n : ℕ) (i : Fin (n + 1)) (k : Fin ((i : ℕ) + 2)) :
    awTensorTerm C D (SimplexCategory.δ k ≫ awFront (n + 1) i.succ)
      (awBack (n + 1) i.succ) (by have := i.isLt; simp only [Fin.val_succ]; omega) =
        awHorizontalFaceTerm C D n i k := by
  rw [awFront_eq_interval, awBack_eq_interval]
  exact awTensorTerm_interval_congr C D _ (by simp) _ _ _ _

/-- 概要：水平境界の非対角項は削除後の切断の項に等しい。
方針：一般の前半の境界項の同定を、実切断の次数に特殊化する。
規約：KST A.5、局所削除点 k≤i。
使われ方：水平境界和の添字変換。 -/
lemma awHorizontalFaceTerm_nonDiagonal (n : ℕ) (i : Fin (n + 1)) (k : Fin ((i : ℕ) + 1)) :
    awHorizontalFaceTerm C D n i k.castSucc =
      awDeletedFaceTerm C D n (⟨k, by have := k.isLt; have := i.isLt; omega⟩ : Fin (n + 2)) i := by
  dsimp only [awHorizontalFaceTerm, awDeletedFaceTerm]
  rw [awFront_eq_interval, awBack_eq_interval]
  exact awLeftBoundaryTerm C D (awDegrees n i) k

/-- 概要：垂直境界の非対角項は削除後の切断の項に等しい。
方針：一般の後半の境界項の同定を実切断の次数に特殊化する。
規約：KST A.5、局所削除点 k+1。
使われ方：垂直境界和の添字変換。 -/
lemma awVerticalFaceTerm_nonDiagonal (n : ℕ) (i : Fin (n + 1))
    (k : Fin (n - (i : ℕ) + 1)) :
    awVerticalFaceTerm C D n i k.succ =
      awDeletedFaceTerm C D n
        (⟨(i : ℕ) + ((k : ℕ) + 1), by have := k.isLt; have := i.isLt; omega⟩ : Fin (n + 2)) i := by
  dsimp only [awVerticalFaceTerm, awDeletedFaceTerm]
  rw [awFront_eq_interval, awBack_eq_interval]
  exact awRightBoundaryTerm C D (awDegrees n i) k

/-- 概要：水平境界の最後の面は共通の対角項。
方針：前半の最後の頂点の削除を評価する。
規約：KST A.5。使われ方：隣接する切断点の対角項の相殺。 -/
lemma awHorizontalFaceTerm_diagonal (n : ℕ) (i : Fin (n + 1)) :
    awHorizontalFaceTerm C D n i (Fin.last ((i : ℕ) + 1)) = awCutDiagonalTerm C D n i := by
  dsimp only [awHorizontalFaceTerm, awCutDiagonalTerm]
  rw [awInterval_face_last]

/-- 概要：垂直境界の最初の面は共通の対角項。
方針：後半の最初の頂点の削除を評価する。
規約：KST A.5。使われ方：水平境界の対角項との相殺。 -/
lemma awVerticalFaceTerm_diagonal (n : ℕ) (i : Fin (n + 1)) :
    awVerticalFaceTerm C D n i 0 = awCutDiagonalTerm C D n i := by
  dsimp only [awVerticalFaceTerm, awCutDiagonalTerm]
  rw [awInterval_face_zero]

/-- 概要：実水平境界を共通の区間座標の有限和で表す。
方針：各水平境界項の区間の長さを整理する。
規約：KST A.5。使われ方：非対角項と対角項の分離。 -/
lemma awHorizontal_boundary_model (n : ℕ) :
    alexanderWhitneyApp C D (n + 1) ≫
      mapBifunctor.D₁ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) (n + 1) n =
      ∑ i : Fin (n + 1), ∑ k : Fin ((i : ℕ) + 2), (-1 : ℤ) ^ (k : ℕ) •
        awHorizontalFaceTerm C D n i k := by
  rw [alexanderWhitney_horizontal_boundary]
  simp_rw [awHorizontalFaceTerm_eq]

/-- 概要：実垂直境界を共通の区間座標の有限和で表す。
方針：前半の制限を区間へ同定する。
規約：KST A.5、垂直符号を保持。使われ方：非対角項と対角項の分離。 -/
lemma awVertical_boundary_model (n : ℕ) :
    alexanderWhitneyApp C D (n + 1) ≫
      mapBifunctor.D₂ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) (n + 1) n =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        (∑ k : Fin (n - (i : ℕ) + 2), (-1 : ℤ) ^ (k : ℕ) • awVerticalFaceTerm C D n i k) := by
  rw [alexanderWhitney_vertical_boundary]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  dsimp only [awVerticalFaceTerm]
  rw [awFront_eq_interval]
  rfl

/-- 概要：一つの切断点の水平境界和を非対角項と最後の対角項に分ける。
方針：最後の面を分離し、各制限項の同定を使う。
規約：KST A.5。使われ方：全境界の非対角和と対角和の整理。 -/
lemma awHorizontal_sum_split (n : ℕ) (i : Fin (n + 1)) :
    (∑ k : Fin ((i : ℕ) + 2), (-1 : ℤ) ^ (k : ℕ) • awHorizontalFaceTerm C D n i k) =
    (∑ k : Fin ((i : ℕ) + 1), (-1 : ℤ) ^ (k : ℕ) • awDeletedFaceTerm C D n
      (⟨k, by have := k.isLt; have := i.isLt; omega⟩ : Fin (n + 2)) i) +
      (-1 : ℤ) ^ ((i : ℕ) + 1) • awCutDiagonalTerm C D n i := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, awHorizontalFaceTerm_nonDiagonal,
    awHorizontalFaceTerm_diagonal]

/-- 概要：一つの切断点の垂直境界和を最初の対角項と非対角項に分ける。
方針：最初の面を分離し、二つの交代符号を掛ける。
規約：KST A.5、符号の積は全削除点の符号。
使われ方：垂直境界和を source の境界の符号に合わせる。 -/
lemma awVertical_sum_split (n : ℕ) (i : Fin (n + 1)) :
    (-1 : ℤ) ^ (i : ℕ) •
      (∑ k : Fin (n - (i : ℕ) + 2), (-1 : ℤ) ^ (k : ℕ) • awVerticalFaceTerm C D n i k) =
    (-1 : ℤ) ^ (i : ℕ) • awCutDiagonalTerm C D n i +
    (∑ k : Fin (n - (i : ℕ) + 1), (-1 : ℤ) ^ ((i : ℕ) + ((k : ℕ) + 1)) •
      awDeletedFaceTerm C D n
        (⟨(i : ℕ) + ((k : ℕ) + 1), by have := k.isLt; have := i.isLt; omega⟩ : Fin (n + 2)) i) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, awVerticalFaceTerm_diagonal,
    awVerticalFaceTerm_nonDiagonal, smul_add, Finset.smul_sum, smul_smul, ← pow_add, Fin.val_succ]

/-- 概要：Alexander–Whitney の成分は実際の鎖複体の微分と可換。
方針：左右の非対角境界和を削除後の切断へ移し、対角和を相殺する。
規約：KST Construction A.5 の標準 AW、引用や追加公理を使わない。
使われ方：正規化への射影と shuffle との比較に渡す鎖写像。 -/
@[kerodon 00S3]
theorem alexanderWhitney_comm (n : ℕ) :
    alexanderWhitneyApp C D (n + 1) ≫
      (chainIntegerTensor ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D)).d (n + 1) n =
    ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n ≫
      alexanderWhitneyApp C D n := by
  let L := ∑ i : Fin (n + 1), ∑ k : Fin ((i : ℕ) + 1), (-1 : ℤ) ^ (k : ℕ) •
    awDeletedFaceTerm C D n (⟨k, by have := k.isLt; have := i.isLt; omega⟩ : Fin (n + 2)) i
  let R := ∑ i : Fin (n + 1), ∑ k : Fin (n - (i : ℕ) + 1),
    (-1 : ℤ) ^ ((i : ℕ) + ((k : ℕ) + 1)) • awDeletedFaceTerm C D n
      (⟨(i : ℕ) + ((k : ℕ) + 1), by have := k.isLt; have := i.isLt; omega⟩ : Fin (n + 2)) i
  let P := ∑ i : Fin (n + 1), (-1 : ℤ) ^ ((i : ℕ) + 1) • awCutDiagonalTerm C D n i
  let Q := ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • awCutDiagonalTerm C D n i
  have hD : P + Q = 0 := by
    dsimp only [P, Q]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    exact awDiagonal_sign_cancel i (awCutDiagonalTerm C D n i)
  have hB : L + R = ∑ k : Fin (n + 2), ∑ i : Fin (n + 1),
      (-1 : ℤ) ^ (k : ℕ) • awDeletedFaceTerm C D n k i :=
    awBoundaryCoordinates_sum n (fun p ↦ (-1 : ℤ) ^ (p.1 : ℕ) • awDeletedFaceTerm C D n p.1 p.2)
  calc
    _ = (L + P) + (Q + R) := by
      rw [mapBifunctor.d_eq, Preadditive.comp_add, awHorizontal_boundary_model,
        awVertical_boundary_model]
      simp_rw [awHorizontal_sum_split, awVertical_sum_split]
      simp only [Finset.sum_add_distrib]
      rfl
    _ = (L + R) + (P + Q) := by abel
    _ = L + R := by rw [hD, add_zero]
    _ = ∑ k : Fin (n + 2), ∑ i : Fin (n + 1),
        (-1 : ℤ) ^ (k : ℕ) • awDeletedFaceTerm C D n k i := hB
    _ = _ := by
      rw [alexanderWhitney_source_boundary]
      simp only [awDeletedFaceTerm, Finset.smul_sum]

/-- 概要：標準 Alexander–Whitney の実鎖写像。
方針：共有切断点の有限和の成分に、証明済みの微分との可換性を付ける。
規約：KST Construction A.5、正規化前の交代面写像複体。
使われ方：Moore 複体への射影と Eilenberg–Zilber の標準比較。 -/
@[kerodon 00S3]
def alexanderWhitney :
    (alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D) ⟶
      chainIntegerTensor ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) :=
  ChainComplex.ofHom (alexanderWhitneyApp C D) (alexanderWhitney_comm C D)

/-- 概要：標準 AW の鎖写像は二つの単体的整数加群の射に自然。
方針：証明済みの各次数の成分の自然性を鎖写像の等式へ束ねる。
規約：KST A.5、外部 G の作用の準同型も含む。
使われ方：正規化した比較の関手性と同変性。 -/
lemma alexanderWhitney_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') :
    (alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g) ≫
        alexanderWhitney C' D' =
      alexanderWhitney C D ≫
        chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
          ((alternatingFaceMapComplex _).map g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change integerTensorMap (f.app (op ⦋n⦌)) (g.app (op ⦋n⦌)) ≫
    alexanderWhitneyApp C' D' n = _
  exact alexanderWhitneyApp_naturality f g n

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.2.3.22" (partial := special) "仮定：二つの整数加群値単体的対象（Lean が強い：一般の n 変数の多重加法関手でなくテンソルの場合）。結論：前面と後面を取り全次数の分割について加える Alexander–Whitney 写像（二変数の場合は一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney
attribute [cite HA "1.2.3.24" (partial := special) "仮定：整数加群の単体的対象二つとそれぞれの射（Lean が強い：二変数テンソルに特化）。結論：正規化・非正規化の Alexander–Whitney 写像が各射について可換（二変数の場合は一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_naturality
attribute [cite HA "1.2.3.26" (partial := component) "仮定：整数加群のテンソル（Lean が強い：一般の冪等完備な加法的モノイダル圏ではない）。結論：正規化と非正規化それぞれのテンソル比較射。一般の両関手の oplax monoidal 構造を返す型は含まれない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney
