module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCoefficientLayerIsos
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellLayerHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassLayerMaps
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassTargetModel

/-!
概要：二切断候補の元の class 模型への両比較射の H⁻² 作用を計算する。
方針：底変更は係数上で恒等であり、cell から摂動模型への比較も同じ層を保つ。
規約：標的比較の準同型性を仮定しない。使われ方：実 roof 全体の π₂ 作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma sourceToCellModel_layer : homologyMap (d.sourceToCellModel R).hom (-2) ≫
    (postnikovCellModelLayerHomologyIso R (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom =
      (d.sourceLayerIso R).hom ≫
        (d.sourceCoefficientHomologyIso R).hom := by
  let N := postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) 1
  let q := (d.lowerBaseInverse R).roof.denominator
  have hf : d.sourceCellMap R ≫
      postnikovCellClass R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) =
        d.sourceClass R ≫ SquareZero.baseChangeMap q N := by
    rw [sourceCellMap, sourceClass, Category.assoc, Category.assoc, postnikovCellClassOver_map]
  have h := SquareZeroExtension.layerHomologyIso_map_naturality (d.denominatorLayer R) N
    (d.sourceClass R) (postnikovCellClass R (B.obj d.layerInverse.zero.stage).obj 1 (by omega))
    (d.sourceCellMap R) q (SquareZero.baseChangeMap q N) (𝟙 N.X)
    (SquareZero.baseChangeMap_hom q N) hf (by exact (SquareZero.zeroSection_mapOver _ _ _ _).symm)
    (-2) (d.classSource_homology_zero R _ (by omega))
    (d.classSource_homology_zero R _ (by omega))
    (postnikovCellSource_homology_zero R _ 1 _ (by omega))
    (postnikovCellSource_homology_zero R _ 1 _ (by omega))
  erw [homologyMap_id] at h
  simpa only [sourceToCellModel, postnikovCellModelLayerHomologyIso, sourceLayerIso,
    Iso.trans_hom, homologyMap_id, Category.comp_id, ← Category.assoc,
    sourceCoefficientHomologyIso, targetCoefficientHomologyIso, N, q, id_eq,
    Int.reduceAdd, Int.reduceNeg, sourceModel, targetModel, classBase,
    postnikovCommonClassBase] using
      congrArg (fun t => t ≫
        (d.sourceCoefficientHomologyIso R).hom) h

lemma targetToCellModel_layer : homologyMap (d.targetToCellModel R).hom (-2) ≫
    (postnikovCellModelLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
      (d.targetLayerIso R).hom ≫
        (d.targetCoefficientHomologyIso R).hom := by
  let N := postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1
  let q := d.targetBase R
  have hf : d.targetCellMap R ≫ postnikovCellClass R (A.obj j).obj 1 (by omega) =
      d.targetClass R ≫ SquareZero.baseChangeMap q N := by
    let α := postnikovCommonClassCompatibilityToCell R f d.baseInverse d.layerInverse
    change (α ≫ cellResolutionMap R q) ≫ postnikovCellClass R (A.obj j).obj 1 (by omega) =
      (α ≫ postnikovCellClassOver R (A.obj j).obj (d.classBase R) 1 (by omega) q) ≫
        SquareZero.baseChangeMap q N
    rw [Category.assoc, Category.assoc, postnikovCellClassOver_map]
  have h := SquareZeroExtension.layerHomologyIso_map_naturality (d.numeratorLayer R) N
    (d.targetClass R) (postnikovCellClass R (A.obj j).obj 1 (by omega)) (d.targetCellMap R)
    q (SquareZero.baseChangeMap q N) (𝟙 N.X) (SquareZero.baseChangeMap_hom q N) hf
    (by exact (SquareZero.zeroSection_mapOver _ _ _ _).symm) (-2)
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))
    (postnikovCellSource_homology_zero R _ 1 _ (by omega))
    (postnikovCellSource_homology_zero R _ 1 _ (by omega))
  erw [homologyMap_id] at h
  simpa only [targetToCellModel, postnikovCellModelLayerHomologyIso, targetLayerIso,
    Iso.trans_hom, homologyMap_id, Category.comp_id, ← Category.assoc,
    sourceCoefficientHomologyIso, targetCoefficientHomologyIso, N, q, id_eq,
    Int.reduceAdd, Int.reduceNeg, sourceModel, targetModel, classBase,
    postnikovCommonClassBase] using
      congrArg (fun t => t ≫
        (d.targetCoefficientHomologyIso R).hom) h

lemma sourceToOriginalModel_layer : homologyMap (d.sourceToOriginalModel R).hom (-2) ≫
    (postnikovClassModelLayerHomologyIso R (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom =
      (d.sourceLayerIso R).hom ≫
        (d.sourceCoefficientHomologyIso R).hom := by
  have hc := postnikovCellComparison_layer R (B.obj d.layerInverse.zero.stage).obj 1 (by omega)
  rw [sourceToOriginalModel, Mon.comp_hom', homologyMap_comp]
  calc
    _ = homologyMap (d.sourceToCellModel R).hom (-2) ≫
        (postnikovCellModelLayerHomologyIso R
          (B.obj d.layerInverse.zero.stage).obj 1 (by omega)).hom := by
      simpa only [Category.assoc, Int.reduceAdd, Int.reduceNeg] using
        congrArg (fun t => homologyMap (d.sourceToCellModel R).hom (-2) ≫ t) hc
    _ = _ := d.sourceToCellModel_layer R

lemma targetToOriginalModel_layer : homologyMap (d.targetToOriginalModel R).hom (-2) ≫
    (postnikovClassModelLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom =
      (d.targetLayerIso R).hom ≫
        (d.targetCoefficientHomologyIso R).hom := by
  have hc := postnikovCellComparison_layer R (A.obj j).obj 1 (by omega)
  rw [targetToOriginalModel, Mon.comp_hom', homologyMap_comp]
  calc
    _ = homologyMap (d.targetToCellModel R).hom (-2) ≫
        (postnikovCellModelLayerHomologyIso R (A.obj j).obj 1 (by omega)).hom := by
      simpa only [Category.assoc, Int.reduceAdd, Int.reduceNeg] using
        congrArg (fun t => homologyMap (d.targetToCellModel R).hom (-2) ≫ t) hc
    _ = _ := d.targetToCellModel_layer R

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
