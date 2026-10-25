module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeChosenRightFrame
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

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
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

attribute [local instance] EInfinity.DGAlgebra.modelCategory
  EInfinity.DGAlgebra.hasFiniteLimits EInfinity.DGAlgebra.hasTerminal

def nativeCellChosenMixedMappingFunctor : Mon (Complex R) ⥤ SSet.{u} :=
  EInfinity.FrameHom.rightFrameDiagram (nativeModelRightResolutionFamily R) ⋙
    EInfinity.FrameHom.MixedFrame.mixedFunctor (nativeCellSourceFrame R A)

def nativeCellChosenMixedLeft :
    cosimplicialHom (nativeCellSourceFrame R A) ⟶ nativeCellChosenMixedMappingFunctor R A where
  app B := EInfinity.FrameHom.MixedFrame.leftComparison (nativeCellSourceFrame R A)
    ((EInfinity.FrameHom.rightFrameUnit (nativeModelRightResolutionFamily R)).app B)
  naturality B C f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro h
    have hh := congr_app
      ((EInfinity.FrameHom.rightFrameUnit (nativeModelRightResolutionFamily R)).naturality f) n
    change f ≫ _ = _ ≫ _ at hh
    change (h ≫ f) ≫ _ = (h ≫ _) ≫ _
    rw [Category.assoc, hh, Category.assoc]
    rfl

def nativeCellChosenMixedRight : nativeCellChosenRightMappingFunctor R A ⟶
    nativeCellChosenMixedMappingFunctor R A where
  app B := EInfinity.FrameHom.MixedFrame.rightComparison (nativeCellSourceFrame R A)
    (nativeCellSourceFrameAugmentation R A)
    ((EInfinity.FrameHom.rightFrameDiagram (nativeModelRightResolutionFamily R)).obj B)
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
  have : IsFibrant B := EInfinity.DGAlgebra.allFibrant R B
  exact EInfinity.FrameHom.MixedFrame.leftComparison_isIso (nativeCellSourceFrame R A)
    ((nativeModelSourceResolutionFamily R).cofibrant (cellResolution R A))
    ((EInfinity.FrameHom.rightFrameUnit (nativeModelRightResolutionFamily R)).app B)
    (EInfinity.FrameHom.rightFrameDiagram_isFibrant (nativeModelRightResolutionFamily R) B)
    (fun n => (EInfinity.FrameHom.rightFrameUnit_trivialCofibration
      (nativeModelRightResolutionFamily R) B n).2)

lemma nativeCellChosenMixedRight_anodyneImage_isIso (B : Mon (Complex R)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((nativeCellChosenMixedRight R A).app B)) := by
  have := cellResolution_isCofibrant R A
  exact EInfinity.FrameHom.MixedFrame.rightComparison_isIso (nativeCellSourceFrame R A)
    ((nativeModelSourceResolutionFamily R).cofibrant (cellResolution R A))
    (nativeCellSourceFrameAugmentation R A)
    (fun n => ((nativeModelSourceResolutionFamily R).atObject
      (cellResolution R A)).augmentation_weakEquivalence n)
    ((EInfinity.FrameHom.rightFrameDiagram (nativeModelRightResolutionFamily R)).obj B)
    ((nativeModelRightResolutionFamily R).cofibrant (op B))

lemma nativeCellChosenMixedLeft_weakEquivalence (B : Mon (Complex R)) :
    InfinityCategories.IsWeakHomotopyEquivalence ((nativeCellChosenMixedLeft R A).app B) :=
  EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (nativeCellChosenMixedLeft_anodyneImage_isIso R A B)

lemma nativeCellChosenMixedRight_weakEquivalence (B : Mon (Complex R)) :
    InfinityCategories.IsWeakHomotopyEquivalence ((nativeCellChosenMixedRight R A).app B) :=
  EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (nativeCellChosenMixedRight_anodyneImage_isIso R A B)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
