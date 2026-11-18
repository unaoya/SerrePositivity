module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeCellModel
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMultiplicativeFrame
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialFrameFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.CofibrantBoundary

/-!
概要：実 AW 単体模型を、E2 の実 dg 代数モデルにおける全自然な right frame として束ねる。
方針：元の matching 全射と増大の擬同型性を代入し、反対圏の既存 frame 族にする。
規約：実モデルを局所登録し、モデル構造や frame 条件を仮定入力にしない。
使われ方：元の乗法的写像単体を E2 の right frame 比較へ適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

attribute [local instance] _root_.SerrePositivity.DGAlgebra.modelCategory
  _root_.SerrePositivity.DGAlgebra.hasFiniteLimits _root_.SerrePositivity.DGAlgebra.hasTerminal

local instance : HasInitial (Mon (Complex R))ᵒᵖ := hasInitial_op_of_hasTerminal

local instance : HasInitial (SimplexCategory ⥤ (Mon (Complex R))ᵒᵖ) :=
  (Functor.isInitialConst SimplexCategory
    (initialIsInitial (C := (Mon (Complex R))ᵒᵖ))).hasInitial

lemma multiplicativeSimplices_reedyFibrant (B : Mon (Complex R)) :
    reedyLeft simplex (cofibrations (Mon (Complex R))ᵒᵖ)
      (initial.to (multiplicativeSimplices R B).rightOp) := by
  intro n
  apply ((cofibrations (Mon (Complex R))ᵒᵖ).arrow_iso_iff
    (latchingInitialArrowIso simplex n (multiplicativeSimplices R B).rightOp)).mp
  change _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R (multiplicativeMatchingRestriction R B n).hom
  exact multiplicativeSimplices_matching_fibration R B n

lemma multiplicativeSimplicesAugmentation_weakEquivalence
    (B : Mon (Complex R)) (n : SimplexCategoryᵒᵖ) :
    weakEquivalences (Mon (Complex R)) ((multiplicativeSimplicesAugmentation R B).app n) :=
  multiplicativeSimplicesAugmentation_quasiIso R B n

def multiplicativeRightFrameFunctor :
    (Mon (Complex R))ᵒᵖ ⥤ (SimplexCategory ⥤ (Mon (Complex R))ᵒᵖ) :=
  (multiplicativeSimplicesFunctor R).op ⋙
    (Functor.leftOpRightOpEquiv SimplexCategory (Mon (Complex R))).functor

def multiplicativeRightFrameAugmentation :
    multiplicativeRightFrameFunctor R ⟶ Functor.const SimplexCategory :=
  Functor.whiskerRight (NatTrans.op (multiplicativeSimplicesConstant R))
    (Functor.leftOpRightOpEquiv SimplexCategory (Mon (Complex R))).functor

def multiplicativeRightFrameFamily : CosimplicialFrameFamily (C := (Mon (Complex R))ᵒᵖ) where
  obj := multiplicativeRightFrameFunctor R
  augmentation := multiplicativeRightFrameAugmentation R
  cofibrant B := multiplicativeSimplices_reedyFibrant R B.unop
  weak B n := multiplicativeSimplicesAugmentation_weakEquivalence R B.unop (op n)

def multiplicativeRightFrameMappingFunctor (A : Mon (Complex R)) :
    Mon (Complex R) ⥤ SSet.{u} :=
  (multiplicativeRightFrameFunctor R).rightOp ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
      (evaluation (Mon (Complex R))ᵒᵖ SSet.{u}).obj (op A)

set_option maxHeartbeats 800000 in -- 元の畳み込み写像関手と反対 frame の全自然比較を照合する。
def multiplicativeMappingRightFrameIso (A : Mon (Complex R)) :
    multiplicativeMappingFunctor R A ≅ multiplicativeRightFrameMappingFunctor R A :=
  NatIso.ofComponents
    (fun B => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomIso A (multiplicativeSimplices R B))
    (by
      intro B C f
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro h
      rfl)

lemma multiplicativeMappingRightFrameIso_app (A B : Mon (Complex R))
    (n : SimplexCategoryᵒᵖ) (f : A ⟶ (multiplicativeSimplices R B).obj n) :
    (((multiplicativeMappingRightFrameIso R A).app B).hom.app n) f = f.op := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
