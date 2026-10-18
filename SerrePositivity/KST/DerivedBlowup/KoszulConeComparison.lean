module

public import SerrePositivity.KST.DerivedBlowup.SequenceGeneratorSplit
public import SerrePositivity.KST.DerivedBlowup.ChartSequenceComparison

/-!
概要：KST Def3.1 の有限列の Koszul 外積模型を既存の反復 cone 模型と同定する。
方針：末尾生成元の分解、生成元追加の cone 同型、空列での比較により帰納する。
規約：既存 koszulComplex の列の順序と cochain 規約を保つ。追加公理は使わない。
使われ方：導来チャートの外積 dg 代数の underlying 複体と既存 Koszul API の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {n : ℕ}

/-- 概要：有限列の外積 Koszul 複体の末尾追加はスカラー作用の cone。
方針：自由生成加群の末尾分解を外積に持ち上げ、生成元追加の cone 同型と合成する。
規約：KST Def3.1、最後の関係式が外側。使われ方：有限列比較の帰納段階。 -/
def sequenceExteriorSuccIso (x : Fin (n + 1) → R) :
    sequenceExteriorCochain x ≅
      (scalarConeFunctor (x (Fin.last n))).obj (sequenceExteriorCochain (Fin.init x)) :=
  (exteriorKoszulCochainIso (sequenceGeneratorEquiv (R := R)).symm
    (exteriorProductDifferential (Finsupp.linearCombination R (Fin.init x)) (x (Fin.last n)))
    (Finsupp.linearCombination R x) (sequenceGeneratorJoin_differential x)).symm ≪≫
      exteriorProductConeIso (Finsupp.linearCombination R (Fin.init x)) (x (Fin.last n))

/-- 概要：既存反復 cone Koszul 複体と有限列の外積 Koszul 複体の同型。
方針：空列の単位同型と末尾追加の cone 同型を列の長さについて帰納する。
規約：KST Def3.1、非正則列を含む任意有限列。使われ方：L6 の既存 Koszul API の利用。 -/
def koszulExteriorIso : {n : ℕ} → (x : Fin n → R) → koszulComplex x ≅ sequenceExteriorCochain x
  | 0, x => sequenceExteriorCochain_empty_iso x
  | n + 1, x =>
    (scalarConeFunctor (x (Fin.last n))).mapIso (koszulExteriorIso (Fin.init x)) ≪≫
      (sequenceExteriorSuccIso x).symm

/-- 概要：導来 blowup チャートの反復 cone 複体と外積 dg 代数の underlying 複体の同型。
方針：有限列の Koszul 比較とチャート添字の標準同型を合成する。
規約：KST Def3.1、ここでは複体同型。導来底変更と局所化は別工程。
使われ方：導来チャートの dg 代数に対する既存の Koszul ホモロジー補題。 -/
def derivedChartExteriorIso {r : ℕ} (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    derivedChartComplex a i ≅
      chartExteriorCochain (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i :=
  koszulExteriorIso (chartKoszulSequence a i) ≪≫ chartSequenceExteriorIso a i

end SerrePositivity.KST.DerivedBlowup
