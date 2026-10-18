module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientAbelian
public import SerrePositivity.KST.DerivedGeometry.ExactDerivedEquivalence

/-!
概要：アフィン準連接係数加群層の導来圏と H 加群の導来圏を比較する。
方針：完全な大域切断の同値を複体の準同型による局所化へ降ろす。
規約：全加群層の導来圏内の Dqc との同値はここでは主張しない。
使われ方：Toën §3.2、KST T1′ の実際のアフィン導来比較への入力。
-/

@[expose] public section
noncomputable section
universe u w₁ w₂
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory.{w₁} (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} H)]

/--
概要：アフィン準連接係数加群層の非有界導来圏は左 H 加群の導来圏と同値。
方針：証明済みの完全な大域切断関手の導来化を同値として束ねる。
規約：各項が準連接な複体の導来圏と、全加群層内の Dqc を区別する。
使われ方：Toën §3.2、BvdB Thm 3.1.1 のアフィン計算の入力。
-/
def affineQcohDerivedEquivalence :
    DerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh ≌
      DerivedCategory (ModuleCat.{u} H) :=
  exactDerivedEquivalence (affineQcohΓ (R := R) H)

/--
概要：アフィン準連接複体の導来比較は標準の整数シフトと可換。
方針：完全関手の導来化のシフト比較を使う。
規約：両導来圏のシフトは Mathlib のもの。
使われ方：Toën §3.2 のアフィン導来比較の三角構造。
-/
instance affineQcohDerivedEquivalence_commShift :
    (affineQcohDerivedEquivalence (R := R) H).functor.CommShift ℤ :=
  inferInstanceAs ((exactDerivedEquivalence (affineQcohΓ (R := R) H)).functor.CommShift ℤ)

/--
概要：アフィン準連接導来同値の逆関手のシフト構造。
方針：同じ完全同値の導来化から得た構造を保持する。
規約：逆関手のシフトを独立に選ばない。
使われ方：Toën §3.2 のアフィン比較の三角構造。
-/
instance affineQcohDerivedEquivalence_inverseCommShift :
    (affineQcohDerivedEquivalence (R := R) H).inverse.CommShift ℤ :=
  inferInstanceAs ((exactDerivedEquivalence (affineQcohΓ (R := R) H)).inverse.CommShift ℤ)

/--
概要：アフィン準連接導来同値の単位と余単位はシフトと可換。
方針：一般の完全同値の導来化の整合性を保持する。
規約：同じ同値を使う。
使われ方：Toën §3.2 のアフィン比較の三角構造。
-/
instance affineQcohDerivedEquivalence_equivalenceCommShift :
    (affineQcohDerivedEquivalence (R := R) H).CommShift ℤ :=
  inferInstanceAs ((exactDerivedEquivalence (affineQcohΓ (R := R) H)).CommShift ℤ)

/--
概要：準連接係数複体と H 加群複体の導来比較は三角同値。
方針：一般の完全同値の導来化の三角構造を適用する。
規約：冪等完備化や新しい公理を追加しない。
使われ方：Toën §3.2、KST T1′ のアフィン係数複体。
-/
instance affineQcohDerivedEquivalence_isTriangulated :
    (affineQcohDerivedEquivalence (R := R) H).IsTriangulated :=
  inferInstanceAs ((exactDerivedEquivalence (affineQcohΓ (R := R) H)).IsTriangulated)

/--
概要：同値の関手は同じ準連接複体の各項の大域切断を導来像へ送る。
方針：Mathlib の完全関手の導来化の因子分解同型を保持する。
規約：対象の存在だけで比較を済ませず同じ複体との正方形を明示する。
使われ方：Toën §3.2、KST D4 の全加群層の導来圏への比較の接続点。
-/
def affineQcohDerivedSquare :
    DerivedCategory.Q ⋙ (affineQcohDerivedEquivalence (R := R) H).functor ≅
      (affineQcohΓ (R := R) H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (affineQcohΓ (R := R) H).mapDerivedCategoryFactors

end SerrePositivity.KST.DerivedGeometry
