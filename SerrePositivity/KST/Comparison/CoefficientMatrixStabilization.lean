module

public import SerrePositivity.KST.Comparison.MatrixStabilization
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# ホモトピー係数群の行列の安定化

概要：係数群の有限行列を、新しい行と列に群の単位を入れて安定化する。
方針：有限集合の直和の行列を rank の和の有限集合へ移す。
規約：KST Lemma 2.13 の M(π_i A) は群を乗法記法で書いたもの。新しい係数の単位は加法記法の零。
使われ方：ĜL の高次の有限 rank の比較を安定 rank へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：係数群の行列に単位の新しい行と列を付ける準同型。
方針：直和添字の四つのブロックを作り、有限集合の和の同値で添字を変える。
規約：行列積でなく、係数群の点ごとの積を使う。
使われ方：正次数の行列群の安定化。
-/
def coefficientMatrixStabilization (G : Type u) [Group G] (r : ℕ) :
    (Fin r → Fin r → G) →* (Fin (r + 1) → Fin (r + 1) → G) where
  toFun a := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks a (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1))
  map_one' := by
    funext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;> simp [Matrix.reindex_apply, Matrix.fromBlocks]
  map_mul' a b := by
    funext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;> simp [Matrix.reindex_apply, Matrix.fromBlocks]

/--
概要：安定化した係数行列の各ブロックの値。
方針：有限集合の和の同値で戻し、四つのブロックを計算する。
規約：新しい行・列の値は群の単位。
使われ方：高次の係数表示の rank の自然性。
-/
theorem coefficientMatrixStabilization_apply_sum (G : Type u) [Group G] (r : ℕ)
    (a : Fin r → Fin r → G) (i j : Fin r ⊕ Fin 1) :
    coefficientMatrixStabilization G r a (finSumFinEquiv i) (finSumFinEquiv j) =
      match i, j with
      | Sum.inl i, Sum.inl j => a i j
      | _, _ => 1 := by
  cases i <;> cases j <;>
    simp [coefficientMatrixStabilization, Matrix.reindex_apply, Matrix.fromBlocks]

/--
概要：ホモトピー係数群の行列の rank の順序列。
方針：各 rank の点ごとの積の群と単位による安定化を並べる。
規約：rank 零を含む。
使われ方：安定係数行列群の余極限。
-/
def coefficientMatrixRankSequence (G : Type u) [Group G] : ℕ ⥤ GrpCat.{u} :=
  Functor.ofSequence (fun r => GrpCat.ofHom (coefficientMatrixStabilization G r))

/--
概要：群の圏における順序列の余極限の存在を登録する。
方針：Mathlib の実際の filtered colimit の cocone と普遍性を使う。
規約：値宇宙を任意とし、添字圏は自然数とする。
使われ方：安定係数行列群と正次数の群の順序列。
-/
instance grpCat_hasSequentialColimits : HasColimitsOfShape ℕ GrpCat.{u} where
  has_colimit F := HasColimit.mk
    ⟨GrpCat.FilteredColimits.colimitCocone F, GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩

/--
概要：正次数の係数群の安定行列群。
方針：有限 rank の点ごとの積の群の順序余極限を取る。
規約：KST Lemma 2.13 の M(G) の乗法記法の模型。
使われ方：安定 ĜL の正次数の群の具体的な比較先。
-/
def stableCoefficientMatrices (G : Type u) [Group G] : GrpCat.{u} :=
  colimit (coefficientMatrixRankSequence G)

end SerrePositivity.KST.Comparison
