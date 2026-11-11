module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineExtraModel
public import SerrePositivity.BhattScholze.Prismatic.PDCechFrameHomotopy
public import Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.AlgebraicTopology.SimplicialObject.Basic
import all Mathlib.AlgebraicTopology.CechNerve
import all SerrePositivity.BhattScholze.Prismatic.CrystallineExtraModel
import all SerrePositivity.BhattScholze.Prismatic.CrystallineExtraContraction
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve
import all SerrePositivity.BhattScholze.Prismatic.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.PDPolynomialCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 一般の係数での余分な座標の厳密な収縮

## 概要
完備分冪模型の余分な多項式 Čech 座標を零に送る余単体的射を構成し、
交代余面複体の擬同型を示す。

## 方針
切断付き Čech 因子の余単体的ホモトピーを、余積・完備化・係数加群へ移す。

## 規約
係数環は任意。δ 構造そのものを新しく構成せず、正の反復 δ 座標に対応する自由座標の因子を扱う。

## 使われ方
BS 著者版 Theorem 5.2 の余分な座標の収縮の古典的な部分。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SerrePositivity.Cosimplicial
open SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

private def rawExtraRetraction : crystallineExtraRaw k r ⟶ pdRawModel k r :=
  Functor.whiskerRight
    (NatTrans.prod' (𝟙 (pdRawModel k r))
      (cechRetraction (extraCechArrow k r) (extraCechSection k r) (extraCechSection_comp k r)))
    crystallineAlgebraCoprod ≫ (baseCoprodIso k r).inv

/-- 完備化後も余分な座標を零に送る余単体的射。 -/
def pdExtraCoordinatesRetraction : withExtraCoords p k r ⟶ pdModel p k r :=
  Functor.whiskerRight (rawExtraRetraction k r)
    (principalCompletionUnder p (CommRingCat.of k))

/-- 余分な座標を加えてから零に戻す合成は、余単体的環の段階で恒等射。 -/
theorem insertPdFactor_retraction :
    insertPdFactor p k r ≫ pdExtraCoordinatesRetraction p k r = 𝟙 (pdModel p k r) := by
  let π := cechRetraction (extraCechArrow k r) (extraCechSection k r) (extraCechSection_comp k r)
  have hab : crystallineAddSplitCech (extraCechArrow k r) (pdRawModel k r) ≫
      Functor.whiskerRight (NatTrans.prod' (𝟙 (pdRawModel k r)) π)
        crystallineAlgebraCoprod = 𝟙 _ := by
    apply NatTrans.ext
    funext n
    change coprod.map (𝟙 _) ((extraCechArrow k r).augmentedCechConerve.hom.app n) ≫
      coprod.map (𝟙 _) (π.app n) = 𝟙 _
    rw [coprod.map_map]
    have hp := NatTrans.congr_app
      (cechAugmentation_retraction (extraCechArrow k r) (extraCechSection k r)
        (extraCechSection_comp k r)) n
    change (extraCechArrow k r).augmentedCechConerve.hom.app n ≫ π.app n = 𝟙 _ at hp
    rw [Category.id_comp, hp, coprod.map_id_id]
  have hraw : rawInsertPdFactor k r ≫ rawExtraRetraction k r = 𝟙 _ := by
    change ((baseCoprodIso k r).hom ≫ _) ≫ (_ ≫ (baseCoprodIso k r).inv) = _
    rw [Category.assoc, ← Category.assoc (crystallineAddSplitCech _ _) _, hab]
    simp
  change Functor.whiskerRight (rawInsertPdFactor k r) _ ≫
    Functor.whiskerRight (rawExtraRetraction k r) _ = _
  rw [← Functor.whiskerRight_comp, hraw]
  apply NatTrans.ext
  funext n
  exact (principalCompletionUnder p (CommRingCat.of k)).map_id _

/-- 完備化と係数加群への移行の後の、余分な座標因子の明示的な余鎖ホモトピー同値。 -/
def pdExtraCoordinatesCochainEquiv :
    HomotopyEquiv
      ((alternatingCofaceMapComplex (ModuleCat k)).obj
        (pdModel p k r ⋙ PDCechNerve.algebraModule k))
      ((alternatingCofaceMapComplex (ModuleCat k)).obj
        (withExtraCoords p k r ⋙ PDCechNerve.algebraModule k)) := by
  let F := principalCompletionUnder p (CommRingCat.of k) ⋙ PDCechNerve.algebraModule k
  let L := alternatingCofaceMapComplex (ModuleCat k)
  exact (HomotopyEquiv.ofIso (L.mapIso (Functor.isoWhiskerRight (baseCoprodIso k r) F))).trans
    (cechSplitCochainEquiv (extraCechArrow k r) (extraCechSection k r)
      (extraCechSection_comp k r) (pdRawModel k r) (crystallineAlgebraCoprod ⋙ F))

/-- 収縮は交代余面複体に移すと上の具体的なホモトピー逆となる。 -/
theorem pdExtraCoordinatesRetraction_cochain :
    (alternatingCofaceMapComplex (ModuleCat k)).map
      (Functor.whiskerRight (pdExtraCoordinatesRetraction p k r) (PDCechNerve.algebraModule k)) =
        (pdExtraCoordinatesCochainEquiv p k r).inv := by
  let F := principalCompletionUnder p (CommRingCat.of k) ⋙ PDCechNerve.algebraModule k
  let L := alternatingCofaceMapComplex (ModuleCat k)
  change L.map (Functor.whiskerRight (rawExtraRetraction k r) F) = _
  dsimp only [rawExtraRetraction]
  rw [Functor.whiskerRight_comp, L.map_comp]
  rfl

/-- 任意の係数環において余分な座標の収縮は擬同型。 -/
theorem pdExtraCoordinatesRetraction_quasiIso :
    QuasiIso ((alternatingCofaceMapComplex (ModuleCat k)).map
      (Functor.whiskerRight (pdExtraCoordinatesRetraction p k r) (PDCechNerve.algebraModule k))) := by
  rw [pdExtraCoordinatesRetraction_cochain]
  exact (pdExtraCoordinatesCochainEquiv p k r).quasiIso_inv

end SerrePositivity.BhattScholze.Prismatic
