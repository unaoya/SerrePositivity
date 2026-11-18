module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.TensorComponents
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# 自然数鎖複体の負次数への延長

概要：Berger–Fresse §1.1 の鎖次数を負の整数コチェイン次数へ移す比較を整備する。
方針：複体の次数埋め込みの既存 API を使い、正次数の零成分を除く。
規約：微分は鎖次数で −1、整数コチェイン次数で +1。
使われ方：AW 対角と既存の Barratt–Eccles コチェイン模型との接続。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NegativeTensor

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：鎖次数 n をコチェイン次数 −n に置く零延長（Berger–Fresse §1.1）。
方針：次数埋め込み embeddingDownNat に沿って延長する。
規約：正のコチェイン次数は零対象。
使われ方：自然数鎖模型を既存の整数コチェインテンソルへ移す。 -/
abbrev extend (K : ChainComplex (ModuleCat.{u} A) ℕ) :
    CochainComplex (ModuleCat.{u} A) ℤ := K.extend ComplexShape.embeddingDownNat

/-- 概要：負の整数次数と元の鎖次数との標準同型（Berger–Fresse §1.1）。
方針：埋め込みに沿う延長の次数同型を使う。
規約：n は自然数で、零も含む。
使われ方：テンソルの次数ごとの比較写像を記述する。 -/
def xIso (K : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (_root_.SerrePositivity.NegativeTensor.extend K).X (-(n : ℤ)) ≅ K.X n :=
  K.extendXIso ComplexShape.embeddingDownNat rfl

/-- 概要：延長の正次数成分は零（Berger–Fresse §1.1）。
方針：正整数が次数埋め込みの像にないことを使う。
規約：元の鎖複体の有界性を仮定しない。
使われ方：整数テンソルの正次数成分と余分な直和因子を除く。 -/
lemma isZero_positive (K : ChainComplex (ModuleCat.{u} A) ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((_root_.SerrePositivity.NegativeTensor.extend K).X i) := by
  apply isZero_extend_X
  intro n
  change -(n : ℤ) ≠ i
  omega

/-- 概要：二つの零延長のテンソルも正次数で零（Berger–Fresse §1.1 の次数規約）。
方針：全直和因子で検査し、必ず正次数となる一方の因子を消す。
規約：既存の整数テンソルの全直和を使う。
使われ方：負次数の比較から複体全体の比較を構成する。 -/
lemma tensor_isZero_positive (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (i : ℤ) (hi : 0 < i) : IsZero ((HomologicalComplex.tensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L)).X i) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply mapBifunctor.hom_ext
  intro r s hrs
  change r + s = i at hrs
  by_cases hr : 0 < r
  · exact (Functor.map_isZero (tensorRight ((_root_.SerrePositivity.NegativeTensor.extend L).X s))
      (_root_.SerrePositivity.NegativeTensor.isZero_positive K r hr)).eq_of_src _ _
  · exact (Functor.map_isZero (tensorLeft ((_root_.SerrePositivity.NegativeTensor.extend K).X r))
      (_root_.SerrePositivity.NegativeTensor.isZero_positive L s (by omega))).eq_of_src _ _

/-- 概要：延長の微分を元の鎖微分で表示する（Berger–Fresse §1.1）。
方針：次数埋め込みの延長の微分公式を使う。
規約：隣接しない次数にも成立する。
使われ方：テンソル比較の鎖写像条件。 -/
lemma d_eq (K : ChainComplex (ModuleCat.{u} A) ℕ) (p q : ℕ) :
    (_root_.SerrePositivity.NegativeTensor.extend K).d (-(p : ℤ)) (-(q : ℤ)) =
      (_root_.SerrePositivity.NegativeTensor.xIso K p).hom ≫ K.d p q ≫ (_root_.SerrePositivity.NegativeTensor.xIso K q).inv :=
  K.extend_d_eq ComplexShape.embeddingDownNat rfl rfl

/-- 概要：次数同型の逆方向は微分と可換（Berger–Fresse §1.1）。
方針：延長の微分公式から同型と逆同型を消す。
規約：任意の二つの自然数次数を扱う。
使われ方：テンソル比較の各因子の微分を計算する。 -/
@[reassoc (attr := simp)]
lemma xIso_inv_d (K : ChainComplex (ModuleCat.{u} A) ℕ) (p q : ℕ) :
    (_root_.SerrePositivity.NegativeTensor.xIso K p).inv ≫ (_root_.SerrePositivity.NegativeTensor.extend K).d (-(p : ℤ)) (-(q : ℤ)) =
      K.d p q ≫ (_root_.SerrePositivity.NegativeTensor.xIso K q).inv := by
  rw [_root_.SerrePositivity.NegativeTensor.d_eq]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.NegativeTensor
