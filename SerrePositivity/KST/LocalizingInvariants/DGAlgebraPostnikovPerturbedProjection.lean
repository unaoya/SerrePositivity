module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedExtension
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovExtensionCone
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeQuotient

/-!
概要：Postnikov の微分変更後の実代数から、元の底への次数全射準同型を構成する。
方針：二座標を保つ実 cone 同型で、元の層と kernel の準同型比較へ戻す。
規約：射影の積保存性も証明済み。使われ方：cell 分解上の Postnikov derivation。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

local instance layerLower : (postnikovLayerBimodule R B n).X.IsStrictlyGE (-(n + 1)) :=
  postnikovLayer_lowerBound R B n

local instance layerUpper : (postnikovLayerBimodule R B n).X.IsStrictlyLE (-(n + 1)) :=
  postnikovLayer_upperBound R B n

def postnikovPerturbedExtensionComplexIso :
    (postnikovPerturbedExtension R B n hn).X ≅ postnikovExtensionCone R B n :=
  SquareZeroCone.complexIso (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
    (postnikovLayerInclusion R B n)

def postnikovPerturbedProjection : postnikovPerturbedExtension R B n hn ⟶ postnikov R B n :=
  SquareZeroCone.quotient (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
    (postnikovLayerInclusionBimodule R B n) (-(n + 1)) (by omega)
    (postnikovTransition R B (n + 1) n (by omega)) (postnikovLayerInclusion_transition_zero R B n)

lemma postnikovPerturbedProjection_hom_eq :
    (postnikovPerturbedProjection R B n hn).hom =
      (postnikovPerturbedExtensionComplexIso R B n hn).hom ≫
        postnikovExtensionConeProjection R B n :=
  SquareZeroCone.quotient_hom_eq _ _ _ _ _ _ _

lemma postnikovPerturbedProjection_epi : Epi (postnikovPerturbedProjection R B n hn).hom :=
  SquareZeroCone.quotient_epi _ _ _ _ _ _ _

lemma postnikovPerturbedProjection_quasiIso :
    QuasiIso (postnikovPerturbedProjection R B n hn).hom :=
  SquareZeroCone.quotient_quasiIso _ _ _ _ _ _ _ (postnikovLayerToKernel_quasiIso R B n)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.4.1.29" (partial := component) "仮定：通常可換環 R 上の厳密非正次数の結合的 dg 代数 B、n≥0 と任意の dg cell 源（Lean が強い：この E₁ の dg 模型の場合）。結論：τ≤n+1 B の平方零 class の錐が擬同型 ∞ 局所化で実際に極限錐となり、実 cell 写像空間の錐も極限となる。摂動した左下の代数は τ≤n B に擬同型である（原典の隣接段の pullback の部分に一致）。塔全体の逆極限、零段の離散 Hom 同定、普遍 cotangent による導分の分類は含まれない。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovPerturbedProjection_quasiIso
