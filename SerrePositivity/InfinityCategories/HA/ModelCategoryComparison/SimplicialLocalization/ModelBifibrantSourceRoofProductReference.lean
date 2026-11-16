module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofCornerEvaluation
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofProductCone
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantFramePinchedWeak
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseProjectionWeak
public import SerrePositivity.EInfinity.Hammock.WeakArrowActionEquivalences

/-!
概要：元の積単体の全族から指定次数の同じ pinched Hom への弱な基準射を作る。
方針：元の第一射影、実 frame の弱比較、同じ augmentation の前合成を合成する。
規約：同じ balanced hammock 内で全比較を行い、包含の逆を選ばない。
使われ方：実 roof の全 slice の同じ弱基準族。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped _root_.Simplicial
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite _root_.SerrePositivity.EInfinity.Hammock
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)
  (b : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：元の積単体の全要素の第一射影自身は弱同値。
方針：任意上限の宇宙における同じ射影の弱同値性を使う。
規約：元の指定次数。使われ方：同じ実 frame の弱比較への入口。 -/
lemma modelBifibrantSourceRoofProductFirstNerve_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductFirstNerve X Y q b) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver.firstNerveMap_weak.{v, u} _ _

/-- 概要：元の積単体から同じ balanced hammock Hom への実基準射。
方針：同じ第一射影と元の frame 比較を合成する。
規約：元の全族。使われ方：同じ次数の augmentation 前合成。 -/
def modelBifibrantSourceRoofProductHammockMap :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductFirstNerve X Y q b ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameColimitMap X Y q

/-- 概要：同じ指定次数の augmentation の前合成。
方針：元の二列 hammock の同じ前合成作用を使う。
規約：同じ実 augmentation。使われ方：指定次数の pinched 基準族。 -/
def modelBifibrantSourceRoofDegreePrecompose :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X q).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegree X Y q b)))
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)

/-- 概要：元の指定次数の augmentation の前合成自身は弱同値。
方針：同じ弱な augmentation の実 hammock 前合成を反転する。
規約：元の実射。使われ方：同じ全積単体の弱比較。 -/
lemma modelBifibrantSourceRoofDegreePrecompose_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreePrecompose X Y q b) :=
  WeakArrow.precompose_forward_isWeakHomotopyEquivalence
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X q).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegree X Y q b))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation_weak X q _) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)

/-- 概要：元の積単体を同じ指定次数の balanced hammock Hom へ送る。
方針：元の全 frame 比較と同じ augmentation の前合成を合成する。
規約：元の全単体。使われ方：native 評価 roof の基準射。 -/
def modelBifibrantSourceRoofProductDegreeHammockMap :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductHammockMap X Y q b ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreePrecompose X Y q b

/-- 概要：元の積単体から同じ指定次数の pinched Hom への実基準射。
方針：同じ balanced hammock 比較の後に Ex∞ 単位と coherent Hom 比較を置く。
規約：元の局所化頂点。使われ方：実屋根比較の全 interval 族への照合。 -/
def modelBifibrantSourceRoofProductPinchedReferenceMap :
    nerve (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductElements X Y q b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantHammockVertex
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreeObject X Y q b)) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantHammockVertex Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductDegreeHammockMap X Y q b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreeObject X Y q b))
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)

/-- 概要：同じ弱基準族を元の comma 全族へ厳密に戻す。
方針：元の積単体・comma の実同型の逆を前合成する。
規約：同じ pinched 基準射。使われ方：全 interval 族の比較。 -/
def modelBifibrantSourceRoofProductCommaReferenceMap :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductPinchedReferenceMap X Y q b

variable [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
include r in
/-- 概要：元の全積単体の同じ balanced hammock 比較射は弱同値。
方針：同じ第一射影と実 frame 比較の弱同値性を合成する。
規約：第一分解と指定 right frame。使われ方：同じ次数の弱基準族。 -/
lemma modelBifibrantSourceRoofProductHammockMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductHammockMap X Y q b) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductFirstNerve_weak X Y q b).comp
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameColimitMap_weak X Y q r)

include r in
/-- 概要：元の全積単体の同じ指定次数の hammock 比較は弱同値。
方針：同じ元の弱比較と augmentation の前合成を合成する。
規約：同じ実射。使われ方：native pinched 比較の弱基準射。 -/
lemma modelBifibrantSourceRoofProductDegreeHammockMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductDegreeHammockMap X Y q b) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductHammockMap_weak X Y q b r).comp
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreePrecompose_weak X Y q b)

include r in
/-- 概要：元の全積単体から同じ指定次数の pinched 基準射自身は弱同値。
方針：同じ hammock 比較と Ex∞ 単位・coherent Hom 比較を合成する。
規約：元の全基準族を保持。使われ方：実 roof の全 slice の弱可縮性。 -/
lemma modelBifibrantSourceRoofProductPinchedReferenceMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductPinchedReferenceMap X Y q b) := by
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreeObject X Y q b))
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
      (SSet.anodyneExtensions.Q_inverts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne _))
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductDegreeHammockMap_weak X Y q b r).comp
    (hu.comp (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap_weak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofDegreeObject X Y q b))
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)))

include r in
/-- 概要：元の comma 上の同じ全 pinched 基準族は弱同値。
方針：同じ実同型の逆と元の弱基準射を合成する。
規約：元の全パラメータ。使われ方：実屋根の全 interval 三角形の判定。 -/
lemma modelBifibrantSourceRoofProductCommaReferenceMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaReferenceMap X Y q b) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaIso X Y q b).inv (by infer_instance)).comp
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductPinchedReferenceMap_weak X Y q b r)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
