module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLeftRoof
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FrameSpanNerve
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ResolutionSpecialSpans
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrow
public import SerrePositivity.EInfinity.Hammock.ReducedColimit
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SpecialThreeArrowComparison

/-!
# 同じ cofibrant 分解の二列と恒等右脚の三列の照合

概要：元の全単体の二列へ恒等右脚を挿入すると元の三本矢の全図式に一致する。
方針：元の cut に沿う全縦射を照合する。
規約：元の分解・単体・全作用素を保持する。
使われ方：source frame の既存 reduced 比較を二列の比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X) (Y : C)

def resolutionLeftRoofFunctor : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofFunctor (weakEquivalences C) q.obj q.augmentation q.augmentation_weakEquivalence
    (fun a => q.homotopicallyConstant a)

lemma resolutionLeftRoofFunctor_insert :
    resolutionLeftRoofFunctor q Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertRightIdentity =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionSpecialSpanFunctor q (𝟙 Y) ((trivialCofibrations C).id_mem Y) ⋙
        _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison.inclusion X Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor := by
  have ho (s : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertRightIdentity ((resolutionLeftRoofFunctor q Y).obj s) =
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionSpecialSpanFunctor q (𝟙 Y) ((trivialCofibrations C).id_mem Y) ⋙
          _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison.inclusion X Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor).obj s :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertRightIdentity_obj (weakEquivalences C) (q.augmentation.app s.unop.obj.unop)
      (q.augmentation_weakEquivalence _) s.unop.val
  apply CategoryTheory.Functor.hext ho
  intro s t a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho s) (ho t)
  intro j
  change HEq (((resolutionLeftRoofFunctor q Y).map a).app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertRightIdentity.cut j)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertRightIdentity_cut]
  fin_cases j <;> rfl

def resolutionLeftRoofNerveMap :
    nerve (ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofNerveMap (weakEquivalences C) q.obj q.augmentation q.augmentation_weakEquivalence
    (fun a => q.homotopicallyConstant a)

lemma resolutionLeftRoofNerveMap_insert :
    resolutionLeftRoofNerveMap q Y ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertRightIdentity) =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameElementSpanNerveMap (trivialFibrations C) (trivialCofibrations C)
        q.obj q.augmentation (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionAugmentation_trivialFibration q) (𝟙 Y)
          ((trivialCofibrations C).id_mem Y) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison.inclusion X Y) ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  change (σ ⋙ ULiftHom.down.{0, v, max u v} ⋙ resolutionLeftRoofFunctor q Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertRightIdentity = _
  rw [CategoryTheory.Functor.assoc, CategoryTheory.Functor.assoc,
    resolutionLeftRoofFunctor_insert]
  rfl

lemma resolutionLeftRoofNerveMap_normalization :
    resolutionLeftRoofNerveMap q Y ≫ _root_.SerrePositivity.EInfinity.Hammock.graphNormalization (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameElementSpanNerveMap (trivialFibrations C) (trivialCofibrations C)
        q.obj q.augmentation (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionAugmentation_trivialFibration q) (𝟙 Y)
          ((trivialCofibrations C).id_mem Y) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison.inclusion X Y) ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor ≫
          _root_.SerrePositivity.EInfinity.Hammock.graphNormalization (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow := by
  have h := _root_.SerrePositivity.EInfinity.Hammock.graphNormalization_naturality (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertRightIdentity
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertRightIdentity) ≫
    _root_.SerrePositivity.EInfinity.Hammock.graphNormalization (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow =
      _root_.SerrePositivity.EInfinity.Hammock.graphNormalization (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word at h
  rw [← h, ← Category.assoc, resolutionLeftRoofNerveMap_insert]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
