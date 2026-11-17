module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.Components
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone

/-!
# テンソルと積全複体の比較の次数成分

## 概要
固定した係数複体とのテンソルを、各行とのテンソルの積全複体へ送る次数ごとの射を作る。

## 方針
テンソルの直和と全複体の積の普遍性を使い、横次数を越えるときの符号を明示する。

## 規約
ここでは次数ごとの射だけを定義する。鎖写像性や擬同型性はこの定義に仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の標準比較射の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.HomologicalAlgebra.CochainProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

/-- 固定係数複体とのテンソルを各行へ施した、厳密な二重複体。 -/
abbrev tensorRows (L : Complex R) (K : CochainComplex (Complex R) ℕ) :
    CochainComplex (Complex R) ℕ :=
  ((cochainTensorFixedLeft L).mapHomologicalComplex (.up ℕ)).obj K

/-- 係数次数 a が横次数 n を越えるときの符号。 -/
def interchangeSign (a : ℤ) (n : ℕ) : ℤˣ := (a * (n : ℤ)).negOnePow

/-- 係数微分の一次数の増加は、標的の横次数の符号と一致する。 -/
theorem interchangeSign_succ_left (a : ℤ) (n : ℕ) :
    interchangeSign (a + 1) n = interchangeSign a n * (n : ℤ).negOnePow := by
  simp only [interchangeSign, add_mul, one_mul, Int.negOnePow_add]

/-- 横微分の一次数の増加では、元のテンソルの符号が相殺する。 -/
theorem interchangeSign_succ_right (a : ℤ) (n : ℕ) :
    a.negOnePow * interchangeSign a (n + 1) = interchangeSign a n := by
  simp only [interchangeSign, Nat.cast_add, Nat.cast_one, mul_add, mul_one,
    Int.negOnePow_add]
  rw [mul_comm (a * (n : ℤ)).negOnePow, ← mul_assoc, Int.units_mul_self, one_mul]

variable (L : Complex R) (K : CochainComplex (Complex R) ℕ)

/-- 指定したテンソルの同次成分から、標的の行成分への標準射。 -/
def tensorComponent (a b q : ℤ) (h : a + b = q) (n : ℕ) :
    L.X a ⊗ (total K).X b ⟶ ((tensorRows L K).X n).X (q - n) :=
  interchangeSign a n • ((L.X a ◁ componentπ K n b) ≫
    ιTensorObj L (K.X n) a (b - n) (q - n) (by omega))

/-- 同次成分からの全ての行への標準射を、積全複体へまとめる。 -/
def tensorSummandComparison (a b q : ℤ) (h : a + b = q) :
    L.X a ⊗ (total K).X b ⟶ (total (tensorRows L K)).X q :=
  componentLift (tensorRows L K) q (tensorComponent L K a b q h)

/-- テンソルの直和の普遍性による、次数ごとの標準比較射。 -/
def tensorComparisonDegree (q : ℤ) :
    (cochainTensor L (total K)).X q ⟶ (total (tensorRows L K)).X q :=
  Sigma.desc (fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} =>
    tensorSummandComparison L K ij.val.1 ij.val.2 q ij.property)

/-- この次数ごとの射の指定同次成分・行成分での公式。 -/
@[reassoc] theorem tensorComparisonDegree_component (a b q : ℤ) (h : a + b = q) (n : ℕ) :
    ιTensorObj L (total K) a b q h ≫ tensorComparisonDegree L K q ≫
        componentπ (tensorRows L K) n q = tensorComponent L K a b q h n := by
  change Sigma.ι (cochainTensorSummand L (total K) q) ⟨(a, b), h⟩ ≫
    Sigma.desc _ ≫ componentπ (tensorRows L K) n q = _
  rw [Sigma.ι_desc_assoc]
  exact componentLift_π (tensorRows L K) q (tensorComponent L K a b q h) n

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
