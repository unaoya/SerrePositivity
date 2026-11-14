module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedClass
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionLift
public import SerrePositivity.KST.LocalizingInvariants.DGDerivationOfMapOver

/-!
概要：元の cell augmentation 上に、非分裂 Postnikov 拡大の実 derivation を構成する。
方針：微分変更代数の全射準同型な射影を cell 分解上で持ち上げ、実 class を合成する。
規約：係数は元の底の shift 層の制限。使われ方：LT の像制限と pro 連結度の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

lemma postnikovPerturbedProjection_surjective (p : ℤ) :
    Function.Surjective ((postnikovPerturbedProjection R B n hn).hom.f p) := by
  have := postnikovPerturbedProjection_epi R B n hn
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

def postnikovCellLift : cellResolution R (postnikov R B n) ⟶
    postnikovPerturbedExtension R B n hn :=
  cellResolutionLift R (postnikovPerturbedProjection R B n hn)
    (postnikovPerturbedProjection_surjective R B n hn)
    (postnikovPerturbedProjection_quasiIso R B n hn)

lemma postnikovCellLift_projection : postnikovCellLift R B n hn ≫
    postnikovPerturbedProjection R B n hn = cellAugmentation R (postnikov R B n) :=
  cellResolutionLift_projection R _ _ _

lemma postnikovCellLift_quasiIso : QuasiIso (postnikovCellLift R B n hn).hom :=
  cellResolutionLift_quasiIso R _ _ _

def postnikovCellClass : cellResolution R (postnikov R B n) ⟶
    postnikovDerivationTarget R B n hn := postnikovCellLift R B n hn ≫
      postnikovPerturbedClass R B n hn

lemma postnikovCellClass_projection : postnikovCellClass R B n hn ≫
    SquareZero.projection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1) =
      cellAugmentation R (postnikov R B n) := by
  rw [postnikovCellClass, Category.assoc, postnikovPerturbedClass_projection,
    postnikovCellLift_projection]

def postnikovCellDerivation : SquareZero.Derivation (cellResolution R (postnikov R B n))
    (bimoduleRestrict (cellAugmentation R (postnikov R B n))
      (postnikovShiftedLayerBimodule R B n hn 1)) :=
  SquareZero.derivationOfMapOver (cellAugmentation R (postnikov R B n))
    (postnikovShiftedLayerBimodule R B n hn 1) (postnikovCellClass R B n hn)
    (postnikovCellClass_projection R B n hn)

lemma postnikovCellDerivation_hom : (postnikovCellDerivation R B n hn).hom =
    (postnikovCellClass R B n hn).hom ≫
      (biprod.snd : (postnikovDerivationTarget R B n hn).X ⟶
        (postnikovShiftedLayerBimodule R B n hn 1).X) := rfl

lemma postnikovCellDerivation_section : (postnikovCellDerivation R B n hn).section ≫
    SquareZero.mapOver (cellAugmentation R (postnikov R B n)) _ _
      (𝟙 (bimoduleRestrict (cellAugmentation R (postnikov R B n))
        (postnikovShiftedLayerBimodule R B n hn 1))) = postnikovCellClass R B n hn :=
  SquareZero.derivationOfMapOver_section _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.4.1.28" (partial := component) "仮定：可換環 R 上の厳密非正次数の結合的 dg 代数 B と n≥0（Lean が強い：この E₁ の dg 模型の場合）。結論：τ≤n+1 B→τ≤n B を、cell resolution 上の実導分の class と零切断の homotopy pullback に底への射を保つ準同型の span で比較する（Postnikov 遷移の平方零表示の部分に一致）。一般の Eₖ と HA の普遍 cotangent による導分との比較は含まれない。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovCellDerivation
