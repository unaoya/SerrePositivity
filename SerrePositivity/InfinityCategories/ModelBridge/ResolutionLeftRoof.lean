module

public import SerrePositivity.EInfinity.FrameHom.FrameLeftRoof
public import SerrePositivity.InfinityCategories.ModelBridge.FrameSpanNerve
public import SerrePositivity.InfinityCategories.ModelBridge.ResolutionSpecialSpans
public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrow
public import SerrePositivity.EInfinity.Hammock.ReducedColimit
public import SerrePositivity.InfinityCategories.ModelBridge.SpecialThreeArrowComparison

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
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra Hammock
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X) (Y : C)

def resolutionLeftRoofFunctor : (((cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ ⥤
    Zigzag (weakEquivalences C) LeftRoof.word X Y :=
  frameLeftRoofFunctor (weakEquivalences C) q.obj q.augmentation q.augmentation_weakEquivalence
    (fun a => q.homotopicallyConstant a)

lemma resolutionLeftRoofFunctor_insert :
    resolutionLeftRoofFunctor q Y ⋙ WordAction.functor LeftRoof.insertRightIdentity =
      resolutionSpecialSpanFunctor q (𝟙 Y) ((trivialCofibrations C).id_mem Y) ⋙
        WeakThreeArrow.inclusion X Y ⋙ ThreeArrow.functor := by
  have ho (s : (((cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ) :
      WordAction.obj LeftRoof.insertRightIdentity ((resolutionLeftRoofFunctor q Y).obj s) =
        (resolutionSpecialSpanFunctor q (𝟙 Y) ((trivialCofibrations C).id_mem Y) ⋙
          WeakThreeArrow.inclusion X Y ⋙ ThreeArrow.functor).obj s :=
    LeftRoof.insertRightIdentity_obj (weakEquivalences C) (q.augmentation.app s.unop.obj.unop)
      (q.augmentation_weakEquivalence _) s.unop.val
  apply CategoryTheory.Functor.hext ho
  intro s t a
  apply Zigzag.hom_hext (ho s) (ho t)
  intro j
  change HEq (((resolutionLeftRoofFunctor q Y).map a).app
    (LeftRoof.insertRightIdentity.cut j)) _
  rw [LeftRoof.insertRightIdentity_cut]
  fin_cases j <;> rfl

def resolutionLeftRoofNerveMap :
    nerve (ULiftHom.{max u v} (((cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ) ⟶
      graph (weakEquivalences C) LeftRoof.word X Y :=
  frameLeftRoofNerveMap (weakEquivalences C) q.obj q.augmentation q.augmentation_weakEquivalence
    (fun a => q.homotopicallyConstant a)

lemma resolutionLeftRoofNerveMap_insert :
    resolutionLeftRoofNerveMap q Y ≫ nerveMap (WordAction.functor LeftRoof.insertRightIdentity) =
      frameElementSpanNerveMap (trivialFibrations C) (trivialCofibrations C)
        q.obj q.augmentation (resolutionAugmentation_trivialFibration q) (𝟙 Y)
          ((trivialCofibrations C).id_mem Y) ≫
        nerveMap (WeakThreeArrow.inclusion X Y) ≫ nerveMap ThreeArrow.functor := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  change (σ ⋙ ULiftHom.down.{0, v, max u v} ⋙ resolutionLeftRoofFunctor q Y) ⋙
      WordAction.functor LeftRoof.insertRightIdentity = _
  rw [CategoryTheory.Functor.assoc, CategoryTheory.Functor.assoc,
    resolutionLeftRoofFunctor_insert]
  rfl

lemma resolutionLeftRoofNerveMap_normalization :
    resolutionLeftRoofNerveMap q Y ≫ graphNormalization (weakEquivalences C) X Y LeftRoof.word =
      frameElementSpanNerveMap (trivialFibrations C) (trivialCofibrations C)
        q.obj q.augmentation (resolutionAugmentation_trivialFibration q) (𝟙 Y)
          ((trivialCofibrations C).id_mem Y) ≫
        nerveMap (WeakThreeArrow.inclusion X Y) ≫ nerveMap ThreeArrow.functor ≫
          graphNormalization (weakEquivalences C) X Y Word.threeArrow := by
  have h := graphNormalization_naturality (weakEquivalences C) X Y LeftRoof.insertRightIdentity
  change nerveMap (WordAction.functor LeftRoof.insertRightIdentity) ≫
    graphNormalization (weakEquivalences C) X Y Word.threeArrow =
      graphNormalization (weakEquivalences C) X Y LeftRoof.word at h
  rw [← h, ← Category.assoc, resolutionLeftRoofNerveMap_insert]
  simp only [Category.assoc]

end SerrePositivity.EInfinity.FrameHom
