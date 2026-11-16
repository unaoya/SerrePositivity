module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeChosenFrameCoherent

/-!
概要：元の代数射を二つの right frame と同じ始域 frame へ送る単位を照合する。
方針：元の増大の前後合成を全次数・全標的で自然に束ね、混合比較の三角形を計算する。
規約：局所化後の生の辺の等式を要求せず、比較に渡す元の単位と厳密三角形を保持する。
使われ方：E2-S (6) の二胞体による零単体・指定底の輸送への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

attribute [local instance] EInfinity.DGAlgebra.modelCategory

def nativeCellMappingUnit :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A) ⟶
      multiplicativeMappingFunctor R (cellResolution R A) :=
  Functor.whiskerRight (multiplicativeSimplicesConstant R)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomFunctor (cellResolution R A))

def nativeCellChosenRightMappingUnit :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A) ⟶
      nativeCellChosenRightMappingFunctor R A :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHomUnit (nativeModelRightResolutionFamily R) (cellResolution R A)

def nativeCellSourceFrameMappingUnit :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily (cellResolution R A) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A) where
  app B :=
    { app n := ↾fun f => (nativeCellSourceFrameAugmentation R A).app n.unop ≫ f
      naturality n m α := by
        apply ConcreteCategory.hom_ext
        intro f
        change (nativeCellSourceFrameAugmentation R A).app m.unop ≫ f =
          (nativeCellSourceFrame R A).map α.unop ≫
            ((nativeCellSourceFrameAugmentation R A).app n.unop ≫ f)
        have ha := (nativeCellSourceFrameAugmentation R A).naturality α.unop
        change (nativeCellSourceFrame R A).map α.unop ≫
          (nativeCellSourceFrameAugmentation R A).app n.unop =
            (nativeCellSourceFrameAugmentation R A).app m.unop ≫ 𝟙 _ at ha
        rw [← Category.assoc, ha, Category.comp_id] }
  naturality B C f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro h
    change (nativeCellSourceFrameAugmentation R A).app n.unop ≫ (h ≫ f) =
      ((nativeCellSourceFrameAugmentation R A).app n.unop ≫ h) ≫ f
    exact (Category.assoc _ _ _).symm

lemma nativeCellMappingUnit_app (B : Mon (Complex R)) (n : SimplexCategoryᵒᵖ)
    (f : cellResolution R A ⟶ B) :
    (((nativeCellMappingUnit R A).app B).app n) f =
      f ≫ (multiplicativeSimplicesAugmentation R B).app n := rfl

lemma nativeCellSourceFrameMappingUnit_app (B : Mon (Complex R)) (n : SimplexCategoryᵒᵖ)
    (f : cellResolution R A ⟶ B) :
    (((nativeCellSourceFrameMappingUnit R A).app B).app n) f =
      (nativeCellSourceFrameAugmentation R A).app n.unop ≫ f := rfl

lemma nativeCellMappingUnit_mixed_triangle :
    nativeCellSourceFrameMappingUnit R A ≫ nativeCellMixedLeft R A =
      nativeCellMappingUnit R A ≫ nativeCellMixedRight R A := by
  apply NatTrans.ext
  funext B
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  change ((nativeCellSourceFrameAugmentation R A).app n.unop ≫ f) ≫
      (multiplicativeSimplicesAugmentation R B).app n =
    (nativeCellSourceFrameAugmentation R A).app n.unop ≫
      (f ≫ (multiplicativeSimplicesAugmentation R B).app n)
  exact Category.assoc _ _ _

lemma nativeCellChosenRightMappingUnit_mixed_triangle :
    nativeCellSourceFrameMappingUnit R A ≫ nativeCellChosenMixedLeft R A =
      nativeCellChosenRightMappingUnit R A ≫ nativeCellChosenMixedRight R A := by
  apply NatTrans.ext
  funext B
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  change ((nativeCellSourceFrameAugmentation R A).app n.unop ≫ f) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit (nativeModelRightResolutionFamily R)).app B).app n =
    (nativeCellSourceFrameAugmentation R A).app n.unop ≫
      (f ≫ ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit (nativeModelRightResolutionFamily R)).app B).app n)
  exact Category.assoc _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
