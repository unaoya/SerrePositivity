module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeChosenRightFrame
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection

/-!
概要：実際に選んだ強い right resolution の Hom を同じ始域 frame と比較する。
方針：元の全自然な rightFrameUnit を混合 Hom の左右の比較へ渡す。
規約：AW frame の増大に Reedy 自明性を追加せず、選んだ実解像だけを使う。
使われ方：E2-S (6) の rightFrameHom と元の AW 模型の全図式比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

attribute [local instance] _root_.SerrePositivity.DGAlgebra.modelCategory
  _root_.SerrePositivity.DGAlgebra.hasFiniteLimits _root_.SerrePositivity.DGAlgebra.hasTerminal

def nativeCellChosenMixedMappingFunctor : Mon (Complex R) ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram (nativeModelRightResolutionFamily R) ⋙
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.mixedFunctor (nativeCellSourceFrame R A)

def nativeCellChosenMixedLeft :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A) ⟶ nativeCellChosenMixedMappingFunctor R A where
  app B := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.leftComparison (nativeCellSourceFrame R A)
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit (nativeModelRightResolutionFamily R)).app B)
  naturality B C f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro h
    have hh := congr_app
      ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit (nativeModelRightResolutionFamily R)).naturality f) n
    change f ≫ _ = _ ≫ _ at hh
    change (h ≫ f) ≫ _ = (h ≫ _) ≫ _
    rw [Category.assoc, hh, Category.assoc]
    rfl

def nativeCellChosenMixedRight : nativeCellChosenRightMappingFunctor R A ⟶
    nativeCellChosenMixedMappingFunctor R A where
  app B := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightComparison (nativeCellSourceFrame R A)
    (nativeCellSourceFrameAugmentation R A)
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram (nativeModelRightResolutionFamily R)).obj B)
  naturality B C f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro h
    change (nativeCellSourceFrameAugmentation R A).app n.unop ≫ (h ≫ _) =
      ((nativeCellSourceFrameAugmentation R A).app n.unop ≫ h) ≫ _
    exact (Category.assoc _ _ _).symm

lemma nativeCellChosenMixedLeft_anodyneImage_isIso (B : Mon (Complex R)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((nativeCellChosenMixedLeft R A).app B)) := by
  have : IsFibrant B := _root_.SerrePositivity.DGAlgebra.allFibrant R B
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftComparison_isIso (nativeCellSourceFrame R A)
    ((nativeModelSourceResolutionFamily R).cofibrant (cellResolution R A))
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit (nativeModelRightResolutionFamily R)).app B)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram_isFibrant (nativeModelRightResolutionFamily R) B)
    (fun n => (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit_trivialCofibration
      (nativeModelRightResolutionFamily R) B n).2)

lemma nativeCellChosenMixedRight_anodyneImage_isIso (B : Mon (Complex R)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((nativeCellChosenMixedRight R A).app B)) := by
  have := cellResolution_isCofibrant R A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightComparison_isIso (nativeCellSourceFrame R A)
    ((nativeModelSourceResolutionFamily R).cofibrant (cellResolution R A))
    (nativeCellSourceFrameAugmentation R A)
    (fun n => ((nativeModelSourceResolutionFamily R).atObject
      (cellResolution R A)).augmentation_weakEquivalence n)
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram (nativeModelRightResolutionFamily R)).obj B)
    ((nativeModelRightResolutionFamily R).cofibrant (op B))

lemma nativeCellChosenMixedLeft_weakEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((nativeCellChosenMixedLeft R A).app B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (nativeCellChosenMixedLeft_anodyneImage_isIso R A B)

lemma nativeCellChosenMixedRight_weakEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((nativeCellChosenMixedRight R A).app B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (nativeCellChosenMixedRight_anodyneImage_isIso R A B)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
