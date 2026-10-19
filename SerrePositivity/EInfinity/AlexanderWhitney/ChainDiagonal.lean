module

public import SerrePositivity.EInfinity.AlexanderWhitney.TensorComponents
public import SerrePositivity.EInfinity.AlexanderWhitney.DifferentialComponents
public import SerrePositivity.EInfinity.AlexanderWhitney.ComponentLaws

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

namespace SerrePositivity.EInfinity.AlexanderWhitney

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped Simplicial TensorProduct

variable (A : Type u) [CommRing A]

local instance (n : ℕ) : Finite {i : ℕ × ℕ // i.1 + i.2 = n} :=
  inferInstanceAs (Finite ((fun i : ℕ × ℕ => i.1 + i.2) ⁻¹' {n}))

local instance (n : ℕ) : Fintype {i : ℕ × ℕ // i.1 + i.2 = n} := Fintype.ofFinite _

/-- 概要：正規化 AW 対角の全次数 n の射（Berger–Fresse §1.1.4）。
方針：有限個の二次数への成分を双積へ束ねる。
規約：テンソル複体は既存の Koszul 符号を使う。
使われ方：AW 鎖写像の次数ごとの射である。 -/
def diagonalDegree (X : SSet.{0}) (n : ℕ) :
    (chains A X).X n ⟶ (HomologicalComplex.tensorObj (chains A X) (chains A X)).X n :=
  tensorLift _ _ n (component A X n)

/-- 概要：AW 対角は次数分割の有限和で与えられる（Berger–Fresse §1.1.4）。
方針：双積への lift を各成分と直和包含の合成の和に展開する。
規約：和の添字は p+q=n を満たす自然数の対である。
使われ方：shuffle と AW の適合性を有限和で計算する。 -/
lemma diagonalDegree_eq_sum (X : SSet.{0}) (n : ℕ) :
    diagonalDegree A X n = ∑ i : {i : ℕ × ℕ // i.1 + i.2 = n},
      component A X n i.val.1 i.val.2 i.property ≫
        ιTensorObj (chains A X) (chains A X) i.val.1 i.val.2 n i.property :=
  tensorLift_eq_sum _ _ _ _

/-- 概要：全次数の AW 射の射影は元の成分に一致する（Berger–Fresse §1.1.4）。
方針：有限双積の lift の射影公式を使う。
規約：p+q=n の任意の指定を許す。
使われ方：微分・自然性・余代数法則を成分で検証する。 -/
@[reassoc (attr := simp)]
lemma diagonalDegree_projection (X : SSet.{0}) (n p q : ℕ) (h : p + q = n) :
    diagonalDegree A X n ≫ tensorProjection (chains A X) (chains A X) n p q h =
      component A X n p q h := tensorLift_projection _ _ _ _ _ _ _

/-- 概要：正規化 AW 対角はテンソル微分と可換（Berger–Fresse §1.1.4）。
方針：全ての二次数に射影し component_d に帰着する。
規約：入力は n+1 次、出力は n 次である。
使われ方：AW 対角を鎖写像として定義する。 -/
lemma diagonalDegree_d (X : SSet.{0}) (n : ℕ) :
    diagonalDegree A X (n + 1) ≫
        (HomologicalComplex.tensorObj (chains A X) (chains A X)).d (n + 1) n =
      (chains A X).d (n + 1) n ≫ diagonalDegree A X n := by
  apply tensorProjection_hom_ext
  intro p q h
  subst n
  rw [Category.assoc, tensor_d_projection]
  simp only [Preadditive.comp_add, Preadditive.comp_zsmul,
    diagonalDegree_projection_assoc, Category.assoc, diagonalDegree_projection]
  exact (component_d A X p q).symm

/-- 概要：正規化 Alexander–Whitney 対角鎖写像（Berger–Fresse §1.1.4）。
方針：有限個の成分を束ね、成分微分公式で鎖写像の条件を証明する。
規約：任意の小さい単体集合、任意の可換環に適用する。
使われ方：EΣ_n の正規化鎖に特殊化して Hopf 対角を得る。 -/
def diagonal (X : SSet.{0}) :
    chains A X ⟶ HomologicalComplex.tensorObj (chains A X) (chains A X) where
  f := diagonalDegree A X
  comm' i j h := by
    obtain rfl : i = j + 1 := h.symm
    exact diagonalDegree_d A X j

/-- 概要：AW 鎖写像の二次数成分は切断公式で与えられる（Berger–Fresse §1.1.4）。
方針：次数ごとの lift の射影公式を用いる。
規約：等式は加群の射の等式である。
使われ方：鎖写像としての対角と成分 API を接続する。 -/
@[reassoc (attr := simp)]
lemma diagonal_projection (X : SSet.{0}) (n p q : ℕ) (h : p + q = n) :
    (diagonal A X).f n ≫ tensorProjection (chains A X) (chains A X) n p q h =
      component A X n p q h := diagonalDegree_projection A X n p q h

/-- 概要：正規化 AW 鎖写像は単体集合の射に自然（Berger–Fresse §1.1.4）。
方針：全次数ごとに二次数への射影を取り、成分の自然性を使う。
規約：単体集合の射の像が退化する場合も含む。
使われ方：Barratt–Eccles の置換作用・単体的合成との適合性を検証する。 -/
lemma diagonal_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    chainMap A f ≫ diagonal A Y =
      diagonal A X ≫ HomologicalComplex.tensorHom (chainMap A f) (chainMap A f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensorProjection_hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Category.assoc, diagonal_projection,
    tensorHom_projection, diagonal_projection_assoc]
  exact component_natural A f n p q h

end SerrePositivity.EInfinity.AlexanderWhitney
