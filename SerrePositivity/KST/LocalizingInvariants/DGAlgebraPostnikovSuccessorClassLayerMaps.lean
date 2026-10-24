module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassLayerIsos
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

/-!
概要：次段切断候補の係数模型射と準同型 zigzag の H⁻⁽ⁿ⁺¹⁾ 作用を元の実係数で計算する。
方針：各実 cospan 射の対角二成分を、元の層ホモロジー自然性へ渡す。
規約：共通源の消滅は構成済み。使われ方：実 roof 候補の πₙ₊₁ 係数の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

lemma sourceToImage_layer : homologyMap (d.sourceToImage R).hom (-(n + 1)) ≫ (d.imageLayerIso R).hom =
    (d.sourceLayerIso R).hom ≫ homologyMap (d.classCoefficient R).hom (-(n + 1) - 1) :=
  SquareZeroExtension.layerHomologyIso_map_naturality (d.denominatorLayer R) (d.numeratorLayer R)
    (d.sourceClass R) (d.imageClass R) (𝟙 (d.classSource R)) (𝟙 (d.classBase R))
    (SquareZero.coefficientMap (d.classBase R) (d.classCoefficient R)) (d.classCoefficient R).hom
    (SquareZero.coefficientMap_hom _ _) (Category.id_comp _)
    ((SquareZeroExtension.map_zeroSection _ _ _ _ _ (SquareZero.coefficientMap_hom _ _)).symm)
    (-(n + 1)) (d.classSource_homology_zero R _ (by omega))
    (d.classSource_homology_zero R _ (by omega))
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))

lemma imageToPath_layer : homologyMap (d.imageToPath R).hom (-(n + 1)) ≫ (d.pathLayerIso R).hom =
    (d.imageLayerIso R).hom := by
  let N := d.numeratorLayer R
  have hb : (𝟙 _ : SquareZero.algebra (d.classBase R) N ⟶
      SquareZero.algebra (d.classBase R) N).hom =
      biprod.map (𝟙 (d.classBase R).X) (𝟙 N.X) := cochainBiprodMap_id.symm
  have hf : MappingPath.section_ R (d.imageClass R) ≫ MappingPath.target R (d.imageClass R) =
      d.imageClass R ≫ 𝟙 _ := by rw [MappingPath.section_target, Category.comp_id]
  have h := SquareZeroExtension.layerHomologyIso_map_naturality N N (d.imageClass R)
    (MappingPath.target R (d.imageClass R)) (MappingPath.section_ R (d.imageClass R))
    (𝟙 (d.classBase R)) (𝟙 _) (𝟙 N.X) hb hf (by simp) (-(n + 1))
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))
    (d.pathSource_homology_zero R _ (by omega)) (d.pathSource_homology_zero R _ (by omega))
  simpa only [imageToPath, PathCospanComparison.originalToPath, pathLayerIso,
    imageLayerIso, homologyMap_id, Category.comp_id] using h

lemma targetToPath_layer : homologyMap (d.targetToPath R).hom (-(n + 1)) ≫ (d.pathLayerIso R).hom =
    (d.targetComposedLayerIso R).hom := by
  let N := d.numeratorLayer R
  have hb : (𝟙 _ : SquareZero.algebra (d.classBase R) N ⟶
      SquareZero.algebra (d.classBase R) N).hom =
      biprod.map (𝟙 (d.classBase R).X) (𝟙 N.X) := cochainBiprodMap_id.symm
  let w := PathCospanComparison.witnessMap R (d.targetClass R) (d.imageClass R)
    (𝟙 (d.classSource R)) (d.comparisonPath R)
  have hf : w ≫ MappingPath.target R (d.imageClass R) =
      (𝟙 (d.classSource R) ≫ d.targetClass R) ≫ 𝟙 _ :=
    (PathCospanComparison.witnessMap_target R _ _ _ _).trans (Category.comp_id _).symm
  have h := SquareZeroExtension.layerHomologyIso_map_naturality N N
    (𝟙 (d.classSource R) ≫ d.targetClass R) (MappingPath.target R (d.imageClass R)) w
    (𝟙 (d.classBase R)) (𝟙 _) (𝟙 N.X) hb hf (by simp) (-(n + 1))
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))
    (d.pathSource_homology_zero R _ (by omega)) (d.pathSource_homology_zero R _ (by omega))
  simpa only [targetToPath, PathCospanComparison.composedToPath, pathLayerIso,
    targetComposedLayerIso, homologyMap_id, Category.comp_id] using h

lemma targetToStandard_layer : homologyMap (d.targetToStandard R).hom (-(n + 1)) ≫
    (d.targetLayerIso R).hom = (d.targetComposedLayerIso R).hom := by
  let N := d.numeratorLayer R
  have hb : (𝟙 _ : SquareZero.algebra (d.classBase R) N ⟶
      SquareZero.algebra (d.classBase R) N).hom =
      biprod.map (𝟙 (d.classBase R).X) (𝟙 N.X) := cochainBiprodMap_id.symm
  have h := SquareZeroExtension.layerHomologyIso_map_naturality N N
    (𝟙 (d.classSource R) ≫ d.targetClass R) (d.targetClass R) (𝟙 (d.classSource R))
    (𝟙 (d.classBase R)) (𝟙 _) (𝟙 N.X) hb (Category.comp_id _).symm (by simp) (-(n + 1))
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))
  rw [targetToStandard, PathCospanComparison.composedToOriginal,
    HomotopyPullbackModel.sourceMap_eq_map]
  simpa only [targetLayerIso, targetComposedLayerIso, homologyMap_id, Category.comp_id] using h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
