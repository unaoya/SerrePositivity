module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.TensorComponents
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.DifferentialComponents
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.ComponentLaws

/-!
# 正規化鎖の Alexander–Whitney 対角

概要：Berger–Fresse §1.1.4 の次数成分をテンソル複体への鎖写像に束ねる。
方針：各全次数の有限双積への lift と成分微分公式を用いる。
規約：自然数の鎖次数を用い、任意の可換環上で定義する。
使われ方：Barratt–Eccles の Hopf 対角の自然数鎖模型となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

local instance _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.instFiniteSubtypeProdNatEqHAddFstSnd_serrePositivity_1 (n : ℕ) : Finite {i : ℕ × ℕ // i.1 + i.2 = n} :=
  inferInstanceAs (Finite ((fun i : ℕ × ℕ => i.1 + i.2) ⁻¹' {n}))

local instance _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.instFintypeSubtypeProdNatEqHAddFstSnd_serrePositivity_1 (n : ℕ) : Fintype {i : ℕ × ℕ // i.1 + i.2 = n} := Fintype.ofFinite _

/-- 概要：正規化 AW 対角の全次数 n の射（Berger–Fresse §1.1.4）。
方針：有限個の二次数への成分を双積へ束ねる。
規約：テンソル複体は既存の Koszul 符号を使う。
使われ方：AW 鎖写像の次数ごとの射である。 -/
def diagonalDegree (X : SSet.{0}) (n : ℕ) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n ⟶ (HomologicalComplex.tensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)).X n :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorLift _ _ n (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n)

/-- 概要：AW 対角は次数分割の有限和で与えられる（Berger–Fresse §1.1.4）。
方針：双積への lift を各成分と直和包含の合成の和に展開する。
規約：和の添字は p+q=n を満たす自然数の対である。
使われ方：shuffle と AW の適合性を有限和で計算する。 -/
lemma diagonalDegree_eq_sum (X : SSet.{0}) (n : ℕ) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree A X n = ∑ i : {i : ℕ × ℕ // i.1 + i.2 = n},
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n i.val.1 i.val.2 i.property ≫
        ιTensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) i.val.1 i.val.2 n i.property :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorLift_eq_sum _ _ _ _

/-- 概要：全次数の AW 射の射影は元の成分に一致する（Berger–Fresse §1.1.4）。
方針：有限双積の lift の射影公式を使う。
規約：p+q=n の任意の指定を許す。
使われ方：微分・自然性・余代数法則を成分で検証する。 -/
@[reassoc (attr := simp)]
lemma diagonalDegree_projection (X : SSet.{0}) (n p q : ℕ) (h : p + q = n) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree A X n ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n p q h =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n p q h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorLift_projection _ _ _ _ _ _ _

/-- 概要：正規化 AW 対角はテンソル微分と可換（Berger–Fresse §1.1.4）。
方針：全ての二次数に射影し component_d に帰着する。
規約：入力は n+1 次、出力は n 次である。
使われ方：AW 対角を鎖写像として定義する。 -/
lemma diagonalDegree_d (X : SSet.{0}) (n : ℕ) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree A X (n + 1) ≫
        (HomologicalComplex.tensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)).d (n + 1) n =
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (n + 1) n ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree A X n := by
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection_hom_ext
  intro p q h
  subst n
  rw [Category.assoc, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensor_d_projection]
  simp only [Preadditive.comp_add, Preadditive.comp_zsmul,
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree_projection_assoc, Category.assoc, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree_projection]
  exact (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_d A X p q).symm

/-- 概要：正規化 Alexander–Whitney 対角鎖写像（Berger–Fresse §1.1.4）。
方針：有限個の成分を束ね、成分微分公式で鎖写像の条件を証明する。
規約：任意の小さい単体集合、任意の可換環に適用する。
使われ方：EΣ_n の正規化鎖に特殊化して Hopf 対角を得る。 -/
def diagonal (X : SSet.{0}) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X ⟶ HomologicalComplex.tensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) where
  f := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree A X
  comm' i j h := by
    obtain rfl : i = j + 1 := h.symm
    exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree_d A X j

/-- 概要：AW 鎖写像の二次数成分は切断公式で与えられる（Berger–Fresse §1.1.4）。
方針：次数ごとの lift の射影公式を用いる。
規約：等式は加群の射の等式である。
使われ方：鎖写像としての対角と成分 API を接続する。 -/
@[reassoc (attr := simp)]
lemma diagonal_projection (X : SSet.{0}) (n p q : ℕ) (h : p + q = n) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X).f n ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n p q h =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n p q h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree_projection A X n p q h

/-- 概要：正規化 AW 鎖写像は単体集合の射に自然（Berger–Fresse §1.1.4）。
方針：全次数ごとに二次数への射影を取り、成分の自然性を使う。
規約：単体集合の射の像が退化する場合も含む。
使われ方：Barratt–Eccles の置換作用・単体的合成との適合性を検証する。 -/
lemma diagonal_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A Y =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X ≫ HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection_hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Category.assoc, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_projection,
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorHom_projection, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_projection_assoc]
  exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_natural A f n p q h

end SerrePositivity.SimplicialChains.AlexanderWhitney
