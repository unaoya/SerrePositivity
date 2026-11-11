module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofAugmentationImage
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductIntervalCriterion
public import SerrePositivity.EInfinity.FrameHom.AnodyneFamilyHomotopy

/-!
概要：元の指定次数の native roof を同じ balanced pinched 基準族と全体で同定する。
方針：元の四列比較と augmentation roof の全等式を同じ余極限で合成する。
規約：全パラメータを保持し、点ごとの類の一致へ置き換えない。
使われ方：実 interval 族の全合成三角形と roof 余終性の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra Opposite SSet Hammock
open SerrePositivity.Reedy SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ積単体の弱基準射を元の comma の第一成分表示で回収する。
方針：元の積単体・comma 同型の第一射影を回収する。
規約：元の実射等式。使われ方：native 評価 roof の全比較。 -/
lemma modelBifibrantSourceRoofProductCommaDegreeHammockMap_transport :
    (modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
      modelBifibrantSourceRoofProductDegreeHammockMap X Y q b =
        modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
          modelBifibrantSourceFrameColimitMap X Y q ≫
            modelBifibrantSourceRoofDegreePrecompose X Y q b := by
  have h : (modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
      modelBifibrantSourceRoofProductFirstNerve X Y q b =
        modelBifibrantSourceRoofProductCommaFirstNerve X Y q b := by
    rw [Iso.inv_comp_eq]
    exact (modelBifibrantSourceRoofProductCommaIso_first X Y q b).symm
  simp only [modelBifibrantSourceRoofProductDegreeHammockMap,
    modelBifibrantSourceRoofProductHammockMap, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, h, Category.assoc]

/-- 概要：元の native 評価 roof は同じ弱基準射の hammock 部分と全体で一致する。
方針：元の四列 source 比較と同じ augmentation roof の厳密な像を使う。
規約：同じ全パラメータ。使われ方：元の pinched 基準族への移送。 -/
lemma modelBifibrantSourceRoofProductCommaEvaluationRoofMap_reference_Q :
    AnodyneHomotopy.anodyneQ.map
      (modelBifibrantSourceRoofProductCommaEvaluationRoofMap X Y q b) =
        AnodyneHomotopy.anodyneQ.map
          ((modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
            modelBifibrantSourceRoofProductDegreeHammockMap X Y q b) := by
  have he := modelBifibrantSourceRoofProductCommaEvaluationRoofMap_sourceComparison X Y q b
  rw [modelBifibrantSourceRoofProductCommaAugmentationRoofMap_image] at he
  have ht := congrArg AnodyneHomotopy.anodyneQ.map
    (modelBifibrantSourceRoofProductCommaDegreeHammockMap_transport X Y q b)
  simpa only [Functor.map_comp, Category.assoc] using he.trans
    (by simpa only [Functor.map_comp, Category.assoc,
      modelBifibrantSourceRoofDegreePrecompose] using ht.symm)

/-- 概要：元の指定次数の native 評価 roof の全 pinched 像。
方針：同じ balanced hammock の Ex∞ 単位と coherent Hom 比較を合成する。
規約：同じ元の局所化頂点。使われ方：native prism の基準族。 -/
def modelBifibrantSourceRoofProductCommaNativePinchedMap :
    nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (modelBifibrantHammockVertex
        (modelBifibrantSourceRoofDegreeObject X Y q b)) (modelBifibrantHammockVertex Y) :=
  modelBifibrantSourceRoofProductCommaEvaluationRoofMap X Y q b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
    kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C (modelBifibrantSourceRoofDegreeObject X Y q b))
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)

/-- 概要：元の native pinched 族は同じ弱な pinched 基準族と全体で一致する。
方針：同じ hammock 部分の全等式へ同じ二つの比較を後合成する。
規約：元の全族。使われ方：全 interval 族の厳密な類の同定。 -/
lemma modelBifibrantSourceRoofProductCommaNativePinchedMap_reference_Q :
    AnodyneHomotopy.anodyneQ.map (modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b) =
      AnodyneHomotopy.anodyneQ.map (modelBifibrantSourceRoofProductCommaReferenceMap X Y q b) := by
  have he := modelBifibrantSourceRoofProductCommaEvaluationRoofMap_reference_Q X Y q b
  simp only [Functor.map_comp] at he
  simp only [modelBifibrantSourceRoofProductCommaNativePinchedMap,
    modelBifibrantSourceRoofProductCommaReferenceMap,
    modelBifibrantSourceRoofProductPinchedReferenceMap, Functor.map_comp]
  rw [he]
  simp only [Category.assoc]

/-- 概要：元の native pinched 全族を同じ二端点の interval 族として露出する。
方針：同じ pinched–interval 比較を合成する。
規約：元の全パラメータ。使われ方：native prism の合成三角形。 -/
def modelBifibrantSourceRoofProductCommaNativeIntervalCell :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)

/-- 概要：同じ native interval 全族の類は元の弱基準 interval 族に一致する。
方針：同じ pinched 全族の反転後の等式を interval の全関手類へ送る。
規約：点ごとの同定で代用しない。使われ方：同じ全三角形の移送。 -/
lemma modelBifibrantSourceRoofProductCommaNativeIntervalCell_eq_reference :
    modelBifibrantSourceRoofProductCommaNativeIntervalCell X Y q b =
      modelBifibrantSourceRoofProductReferenceIntervalCell X Y q b :=
  FrameHom.pinchedFamily_intervalHom_eq_of_anodyneQ_eq _ _
    (modelBifibrantSourceRoofProductCommaNativePinchedMap_reference_Q X Y q b)

variable [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
include r in
/-- 概要：同じ元の native pinched 全族自身は弱同値。
方針：同じ反転後の全等式を元の弱基準族で検出する。
規約：第一分解と指定 right frame。使われ方：実 roof の全弱比較。 -/
lemma modelBifibrantSourceRoofProductCommaNativePinchedMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b) := by
  apply FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence
  rw [modelBifibrantSourceRoofProductCommaNativePinchedMap_reference_Q]
  exact Hammock.anodyneQ_map_isIso_of_weak _
    (modelBifibrantSourceRoofProductCommaReferenceMap_weak X Y q b r)

end SerrePositivity.EInfinity.SimplicialLocalization
