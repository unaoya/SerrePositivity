module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeSourceFrame
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightFrame
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameComparison
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
概要：元の cell 源の AW 写像模型と実始域 frame の Hom を、同じ混合 Hom で比較する。
方針：実余生成モデルの始域 frame と全自然な AW 増大を E2 の比較へ代入する。
規約：同じ比較射を全標的に自然に保持し、∞ 局所化との比較はまだ主張しない。
使われ方：E2-S (6) の指定局所化比較へ渡す、実 frame の選択比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

attribute [local instance] EInfinity.DGAlgebra.modelCategory
  EInfinity.DGAlgebra.hasFiniteLimits EInfinity.DGAlgebra.hasTerminal

def nativeCellMixedMappingFunctor : Mon (Complex R) ⥤ SSet.{u} :=
  multiplicativeSimplicesFunctor R ⋙
    EInfinity.FrameHom.MixedFrame.mixedFunctor (nativeCellSourceFrame R A)

def nativeCellMixedLeft :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A) ⟶ nativeCellMixedMappingFunctor R A where
  app B := EInfinity.FrameHom.MixedFrame.leftComparison (nativeCellSourceFrame R A)
    (multiplicativeSimplicesAugmentation R B)
  naturality B C f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro h
    have hh := congr_app ((multiplicativeSimplicesConstant R).naturality f) n
    change f ≫ (multiplicativeSimplicesAugmentation R C).app n =
      (multiplicativeSimplicesAugmentation R B).app n ≫
        (multiplicativeSimplicesMap R f).app n at hh
    change (h ≫ f) ≫ (multiplicativeSimplicesAugmentation R C).app n =
      (h ≫ (multiplicativeSimplicesAugmentation R B).app n) ≫
        (multiplicativeSimplicesMap R f).app n
    rw [Category.assoc, hh, Category.assoc]

def nativeCellMixedRight : multiplicativeMappingFunctor R (cellResolution R A) ⟶
    nativeCellMixedMappingFunctor R A where
  app B := EInfinity.FrameHom.MixedFrame.rightComparison (nativeCellSourceFrame R A)
    (nativeCellSourceFrameAugmentation R A) (multiplicativeSimplices R B)
  naturality B C f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro h
    change (nativeCellSourceFrameAugmentation R A).app n.unop ≫
        (h ≫ (multiplicativeSimplicesMap R f).app n) =
      ((nativeCellSourceFrameAugmentation R A).app n.unop ≫ h) ≫
        (multiplicativeSimplicesMap R f).app n
    exact (Category.assoc _ _ _).symm

lemma nativeCellMixedLeft_anodyneImage_isIso (B : Mon (Complex R)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((nativeCellMixedLeft R A).app B)) := by
  have : IsFibrant B := EInfinity.DGAlgebra.allFibrant R B
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftComparison_isIso (nativeCellSourceFrame R A)
    ((nativeModelSourceResolutionFamily R).cofibrant (cellResolution R A))
    (multiplicativeSimplicesAugmentation R B)
    (fun n => EInfinity.DGAlgebra.allFibrant R ((multiplicativeSimplices R B).obj n))
    (multiplicativeSimplicesAugmentation_weakEquivalence R B)

lemma nativeCellMixedRight_anodyneImage_isIso (B : Mon (Complex R)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((nativeCellMixedRight R A).app B)) := by
  have := cellResolution_isCofibrant R A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightComparison_isIso (nativeCellSourceFrame R A)
    ((nativeModelSourceResolutionFamily R).cofibrant (cellResolution R A))
    (nativeCellSourceFrameAugmentation R A)
    (fun n => ((nativeModelSourceResolutionFamily R).atObject
      (cellResolution R A)).augmentation_weakEquivalence n)
    (multiplicativeSimplices R B) (multiplicativeSimplices_reedyFibrant R B)

lemma nativeCellMixedLeft_weakEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((nativeCellMixedLeft R A).app B) :=
  EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (nativeCellMixedLeft_anodyneImage_isIso R A B)

lemma nativeCellMixedRight_weakEquivalence (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((nativeCellMixedRight R A).app B) :=
  EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (nativeCellMixedRight_anodyneImage_isIso R A B)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
