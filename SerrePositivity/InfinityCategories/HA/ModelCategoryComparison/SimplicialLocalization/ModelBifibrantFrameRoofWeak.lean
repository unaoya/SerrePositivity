module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.ModelBifibrantFrame
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelRawRelative
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameFunctorImage
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantSourceReducedFirst

/-!
概要：元の bifibrant frame の実二列比較自身を hammock の弱同値へ接続する。
方針：元の包含像の全射等式と ambient frame 比較を、同じ包含の Hom 弱比較で反映する。
規約：第一の関手的分解と指定 right frame のみを使う。
使われ方：実 right Kan 次数比較の余終性への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite _root_.SerrePositivity.EInfinity.Hammock
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories

open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

/-- 概要：元の bifibrant frame の同じ全単体を二列 hammock に送る。
方針：持ち上げた同じ augmentation と元の全作用素を使う。
規約：宇宙調整前の実 frame。使われ方：元の roof の実比較。 -/
def modelBifibrantFrameLeftRoofColimitMap :
    nerve (ULiftHom.{max u v}
      ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrame X q)).obj Y).Elements)ᵒᵖ)) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantWeak (C := C)) X Y :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantWeak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrame X q)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrameAugmentation X q) (fun n => q.augmentation_weakEquivalence n)
    (fun f => q.homotopicallyConstant f)

/-- 概要：元の bifibrant roof 比較の包含像は同じ ambient 比較。
方針：全 frame の相対関手像の厳密な可換式を適用する。
規約：元の全射・全比較を保持。使われ方：ambient 弱同値性の反映。 -/
lemma modelBifibrantFrameLeftRoofColimitMap_image :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantFrameLeftRoofColimitMap X Y q ≫
      Relative.colimitMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantToModel (C := C)) X Y =
        nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameFunctorImageIndex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantToModel (C := C))
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrame X q) Y) ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionLeftRoofColimitMap q Y.obj :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap_functorImage _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantToModel (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrame X q) Y
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrameAugmentation X q) (fun n => q.augmentation_weakEquivalence n)
    (fun f => q.homotopicallyConstant f)

variable [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
include r in
/-- 概要：元の bifibrant frame の同じ二列 hammock 比較射は弱同値。
方針：同じ包含像の三角形と両側の元の弱比較を二対三で消去する。
規約：第二の関手的分解を仮定しない。使われ方：実 roof の余終性判定。 -/
lemma modelBifibrantFrameLeftRoofColimitMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantFrameLeftRoofColimitMap X Y q) := by
  have : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantToModel (C := C)).functor.Full :=
    inferInstanceAs ((BifibrantObject.ι (C := C)).Full)
  have : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantToModel (C := C)).functor.Faithful :=
    inferInstanceAs ((BifibrantObject.ι (C := C)).Faithful)
  apply (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantToModel_colimitMap_weak r X Y).cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantFrameLeftRoofColimitMap_image]
  exact (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameFunctorImageIndex_isWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantToModel (C := C)) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrame X q) Y).comp
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionLeftRoofColimitMap_isWeakHomotopyEquivalence_of_first q Y.obj r
        (MorphismProperty.functorialFactorizationData (cofibrations C) (trivialFibrations C)))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
