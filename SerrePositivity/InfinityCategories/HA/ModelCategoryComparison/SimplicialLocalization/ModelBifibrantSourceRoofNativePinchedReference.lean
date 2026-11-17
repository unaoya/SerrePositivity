module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofAugmentationImage
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofProductIntervalCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.AnodyneFamilyHomotopy

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite _root_.SSet _root_.SerrePositivity.EInfinity.Hammock
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel

open scoped _root_.Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)
  (b : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ積単体の弱基準射を元の comma の第一成分表示で回収する。
方針：元の積単体・comma 同型の第一射影を回収する。
規約：元の実射等式。使われ方：native 評価 roof の全比較。 -/
lemma modelBifibrantSourceRoofProductCommaDegreeHammockMap_transport :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductDegreeHammockMap X Y q b =
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
          _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameColimitMap X Y q ≫
            _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreePrecompose X Y q b := by
  have h : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductFirstNerve X Y q b =
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaFirstNerve X Y q b := by
    rw [Iso.inv_comp_eq]
    exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaIso_first X Y q b).symm
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductDegreeHammockMap,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductHammockMap, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, h, Category.assoc]

/-- 概要：元の native 評価 roof は同じ弱基準射の hammock 部分と全体で一致する。
方針：元の四列 source 比較と同じ augmentation roof の厳密な像を使う。
規約：同じ全パラメータ。使われ方：元の pinched 基準族への移送。 -/
lemma modelBifibrantSourceRoofProductCommaEvaluationRoofMap_reference_Q :
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluationRoofMap X Y q b) =
        AnodyneHomotopy.anodyneQ.map
          ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
            _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductDegreeHammockMap X Y q b) := by
  have he := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluationRoofMap_sourceComparison X Y q b
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaAugmentationRoofMap_image] at he
  have ht := congrArg AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaDegreeHammockMap_transport X Y q b)
  simpa only [Functor.map_comp, Category.assoc] using he.trans
    (by simpa only [Functor.map_comp, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreePrecompose] using ht.symm)

/-- 概要：元の指定次数の native 評価 roof の全 pinched 像。
方針：同じ balanced hammock の Ex∞ 単位と coherent Hom 比較を合成する。
規約：同じ元の局所化頂点。使われ方：native prism の基準族。 -/
def modelBifibrantSourceRoofProductCommaNativePinchedMap :
    nerve (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductComma X Y q b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantHammockVertex
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreeObject X Y q b)) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantHammockVertex Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluationRoofMap X Y q b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreeObject X Y q b))
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)

/-- 概要：元の native pinched 族は同じ弱な pinched 基準族と全体で一致する。
方針：同じ hammock 部分の全等式へ同じ二つの比較を後合成する。
規約：元の全族。使われ方：全 interval 族の厳密な類の同定。 -/
lemma modelBifibrantSourceRoofProductCommaNativePinchedMap_reference_Q :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b) =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaReferenceMap X Y q b) := by
  have he := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluationRoofMap_reference_Q X Y q b
  simp only [Functor.map_comp] at he
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativePinchedMap,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaReferenceMap,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductPinchedReferenceMap, Functor.map_comp]
  rw [he]
  simp only [Category.assoc]

/-- 概要：元の native pinched 全族を同じ二端点の interval 族として露出する。
方針：同じ pinched–interval 比較を合成する。
規約：元の全パラメータ。使われ方：native prism の合成三角形。 -/
def modelBifibrantSourceRoofProductCommaNativeIntervalCell :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)

/-- 概要：同じ native interval 全族の類は元の弱基準 interval 族に一致する。
方針：同じ pinched 全族の反転後の等式を interval の全関手類へ送る。
規約：点ごとの同定で代用しない。使われ方：同じ全三角形の移送。 -/
lemma modelBifibrantSourceRoofProductCommaNativeIntervalCell_eq_reference :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativeIntervalCell X Y q b =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductReferenceIntervalCell X Y q b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedFamily_intervalHom_eq_of_anodyneQ_eq _ _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativePinchedMap_reference_Q X Y q b)

variable [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
include r in
/-- 概要：同じ元の native pinched 全族自身は弱同値。
方針：同じ反転後の全等式を元の弱基準族で検出する。
規約：第一分解と指定 right frame。使われ方：実 roof の全弱比較。 -/
lemma modelBifibrantSourceRoofProductCommaNativePinchedMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativePinchedMap_reference_Q]
  exact _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaReferenceMap_weak X Y q b r)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
