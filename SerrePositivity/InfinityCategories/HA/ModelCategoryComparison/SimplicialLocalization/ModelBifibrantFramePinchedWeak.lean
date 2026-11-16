module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantFrameRoofWeak
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.ModelBifibrantFrameElements
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantRightKanShape
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomPinched
public import SerrePositivity.EInfinity.Hammock.AsSmallComparison

/-!
概要：元の ambient Hom 単体を同じ bifibrant 局所化の pinched Hom へ弱比較する。
方針：元の Hom の包みを戻し、実二列比較と AsSmall の同じ全語同型を合成する。
規約：元の単体・全作用素・局所化頂点を保持する。
使われ方：実屋根の全次数の弱な pinched 基準族。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite _root_.SerrePositivity.EInfinity.Hammock
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

/-- 概要：元の ambient 全 Hom 単体と bifibrant Hom の包みの nerve は実同型。
方針：同じ Hom 同型の順逆を全要素圏へ作用させる。
規約：元の単体・全作用素。使われ方：同じ実二列比較への入口。 -/
def modelBifibrantSourceFrameIndexIso :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) ≅
      nerve (ULiftHom.{max u v}
        ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrame X q)).obj Y).Elements)ᵒᵖ)) where
  hom := { app _ := ↾fun σ => σ ⋙ ULiftHom.down.{0, v, max u v} ⋙
             (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrameHomIso X q Y).inv.mapElements.op ⋙ ULiftHom.up
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun σ => σ ⋙ ULiftHom.down.{0, v, max u v} ⋙
             (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrameHomIso X q Y).hom.mapElements.op ⋙ ULiftHom.up
           naturality _ _ _ := rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    rfl

/-- 概要：元の ambient 全 Hom 単体から同じ bifibrant 二列 hammock への実射。
方針：同じ Hom の包みの同型と元の二列比較を合成する。
規約：元の全単体。使われ方：balanced 模型への実比較。 -/
def modelBifibrantSourceFrameRawColimitMap :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantWeak (C := C)) X Y :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameIndexIso X Y q).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantFrameLeftRoofColimitMap X Y q

/-- 概要：元の全 Hom 単体を同じ balanced bifibrant hammock Hom へ送る。
方針：同じ AsSmall 全語図式の実同型を合成する。
規約：同じ元の二列と両端点。使われ方：実 coherent nerve Hom への比較。 -/
def modelBifibrantSourceFrameColimitMap :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameRawColimitMap X Y q ≫
    (AsSmallComparison.colimitIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantWeak (C := C)) X Y).hom

/-- 概要：元の全 Hom 単体から同じ bifibrant 局所化の pinched Hom への実射。
方針：同じ二列比較の後に Ex∞ 単位と元の coherent Hom 比較を置く。
規約：元の局所化頂点。使われ方：実屋根の全 pinched 基準族。 -/
def modelBifibrantSourceFramePinchedMap :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantHammockVertex X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantHammockVertex Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameColimitMap X Y q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)

variable [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
include r in
/-- 概要：元の ambient 全 Hom 単体の同じ raw bifibrant 比較は弱同値。
方針：同じ実同型と元の frame 比較の弱同値性を合成する。
規約：第一分解と指定 right frame。使われ方：宇宙調整後の弱比較。 -/
lemma modelBifibrantSourceFrameRawColimitMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameRawColimitMap X Y q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameIndexIso X Y q).hom (by infer_instance)).comp
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantFrameLeftRoofColimitMap_weak X Y q r)

include r in
/-- 概要：同じ balanced bifibrant hammock 比較の元の実射は弱同値。
方針：元の raw 弱比較と同じ全語の宇宙同型を合成する。
規約：元の全単体・全作用素。使われ方：実 pinched 比較への入口。 -/
lemma modelBifibrantSourceFrameColimitMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameColimitMap X Y q) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameRawColimitMap_weak X Y q r).comp
    (AsSmallComparison.colimitIso_weak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantWeak (C := C)) X Y)

include r in
/-- 概要：元の全 Hom 単体の同じ bifibrant pinched 比較射は弱同値。
方針：同じ balanced 比較・Ex∞ 単位・coherent Hom 比較の弱同値性を合成する。
規約：同じ元の局所化頂点。使われ方：実屋根 cofinality の弱な基準族。 -/
lemma modelBifibrantSourceFramePinchedMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFramePinchedMap X Y q) := by
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
      (SSet.anodyneExtensions.Q_inverts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne _))
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameColimitMap_weak X Y q r).comp
    (hu.comp (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap_weak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
