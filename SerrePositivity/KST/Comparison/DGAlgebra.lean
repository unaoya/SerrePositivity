module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.GLComponents

/-!
# dg 代数の Γ と ĜL への入口

概要：一対象 dg 圏として表した dg 代数に AW 環と ĜL_r を対応させる。
方針：既存の dg 圏の自己 Hom の構成を一つの対象に特殊化する。
規約：cochain 規約の connective は H^i = 0 (i > 0)。Γ は smart truncation を含む。
使われ方：SS03 (2.9)、KST §2.2、正本 §13-10 の比較定理の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory DifferentialGraded SSet

variable (R : Type u) [CommRing R]

/--
概要：dg 代数を一対象 dg 圏の構造として表す。
方針：既存の Ch(R) 豊穣圏の型をそのまま使い、別の演算法則を追加しない。
規約：合成の順序と Koszul 符号は既存の DGCategory の規約。
使われ方：SS03 (2.9) の単体的環への入力。
-/
abbrev DGAlgebraModel := DGCategory R PUnit.{u + 1}

/--
概要：cochain 規約で dg 代数が connective であること。
方針：正次数の実際の Mathlib homology 対象が零であると述べる。
規約：項自体の正次数消滅より弱い性質。KST §2 と SS03 の chain 規約を反転する。
使われ方：smart truncation を元の dg 代数と比較する際の入力。
-/
def DGAlgebraModel.IsConnective (A : DGAlgebraModel R) : Prop :=
  ∀ i : ℤ, 0 < i → Limits.IsZero ((A.Hom PUnit.unit PUnit.unit).homology i)

/--
概要：dg 代数の smart truncation に Γ の AW 環を対応させる。
方針：一対象 dg 圏の自己 Hom へ SS03 (2.9) の構成を適用する。
規約：一般の入力でも定義でき、connective な場合は全負次数の情報を保つ。
使われ方：KST 式 (2.2) の ΓA。
-/
def dgAlgebraGamma (A : DGAlgebraModel R) : SimplicialObject RingCat.{u} :=
  @gammaEndRingObject R _ PUnit A PUnit.unit

/--
概要：dg 代数の Γ の連結成分の環。
方針：実際の単体集合の π₀ に構成した環構造を使う。
規約：H⁰ との比較は別の宣言で行う。KST 式 (2.2) の下右の係数環。
使われ方：GL_r(π₀A) の定義。
-/
abbrev dgAlgebraComponents (A : DGAlgebraModel R) := π₀ (ringSpace (dgAlgebraGamma R A))

/--
概要：dg 代数の ĜL_r を単体的モノイドとして定義する。
方針：ΓA の行列のうち連結成分で可逆なものを各次数で選ぶ。
規約：KST 式 (2.2)、正本 §13-10。単体的群とはしない。
使われ方：群状モノイドの bar 構成と KST Proposition 2.15。
-/
def dgAlgebraHatGL (A : DGAlgebraModel R) (r : ℕ) : SimplicialObject MonCat.{u} :=
  hatGLMonoidObject (dgAlgebraGamma R A) r

/--
概要：dg 代数の ĜL_r の連結成分は群をなす。
方針：任意の単体的環について証明した群構造を ΓA に適用する。
規約：零次単体の積と単位との整合を持つ。KST 式 (2.2)。
使われ方：群状モノイドとしての bar 構成。
-/
instance dgAlgebraHatGLGroup (A : DGAlgebraModel R) (r : ℕ) :
    Group (π₀ (dgAlgebraHatGL R A r ⋙ forget MonCat)) :=
  hatGLComponentsGroup (dgAlgebraGamma R A) r

/--
概要：dg 代数の ĜL_r の π₀ は成分環の一般線形群である。
方針：単体的環に対する乗法同値を ΓA に適用する。
規約：KST 式 (2.2)。群構造は零次単体の積から誘導される。
使われ方：Segal 1974 Proposition 1.5 の群状性の入力。
-/
def dgAlgebraHatGLComponents (A : DGAlgebraModel R) (r : ℕ) :
    π₀ (dgAlgebraHatGL R A r ⋙ forget MonCat) ≃*
      (Matrix (Fin r) (Fin r) (dgAlgebraComponents R A))ˣ :=
  hatGLComponentsMulEquiv (dgAlgebraGamma R A) r

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.4.1"] _root_.SerrePositivity.KST.Comparison.DGAlgebraModel
