module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGRightTensorComposition
public import SerrePositivity.KST.SConstruction.CubicalLambdaFunctorPairCoherence
public import SerrePositivity.KST.SConstruction.DGFunctorCoherence

/-! # 元の Λ 関手族の実 Perf 右作用の合成
概要：同じ Λ からのラベル族・前入力族・後入力族の作用を、元の入力横合成と比較する。
方針：同じ Serre 対角の自然性・結合と、実右作用の dg 合成等号を合成する。
規約：ラベル・前入力・後入力の順を固定。使われ方：native 全単体の実右作用の合成則。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D E T : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} T]

/-- 同じ Λ からの実 Perf 右作用は、元の二関手族の横合成を厳密に保つ。 -/
lemma cubicalLambdaPerfRightAction_associativity {K : SSet.{u}}
    (X : DGFunctor A (CubicalLambda A K) (PresentedPerfectDGObject A D))
    (F : DGFunctor A (CubicalLambda A K) (DGFunctor A D E))
    (G : DGFunctor A (CubicalLambda A K) (DGFunctor A E T)) :
    DGFunctor.comp
        (cubicalLambdaFunctorPair A
          (DGFunctor.comp (cubicalLambdaFunctorPair A X F)
            (presentedPerfectDGRightTensorAction A D E)) G)
        (presentedPerfectDGRightTensorAction A E T) =
      DGFunctor.comp
        (cubicalLambdaFunctorPair A X
          (DGFunctor.comp (cubicalLambdaFunctorPair A F G) (dgFunctorHorizontalDG A D E T)))
        (presentedPerfectDGRightTensorAction A D T) := by
  have hl := cubicalLambdaFunctorPair_post A (cubicalLambdaFunctorPair A X F) G
    (presentedPerfectDGRightTensorAction A D E) (DGFunctor.id (DGFunctor A E T))
  rw [strictDGFunctor_comp_id] at hl
  have hr := cubicalLambdaFunctorPair_post A X (cubicalLambdaFunctorPair A F G)
    (DGFunctor.id (PresentedPerfectDGObject A D)) (dgFunctorHorizontalDG A D E T)
  rw [strictDGFunctor_comp_id] at hr
  rw [hl, hr, strictDGFunctor_comp_assoc, strictDGFunctor_comp_assoc]
  change DGFunctor.comp (cubicalLambdaFunctorPair A (cubicalLambdaFunctorPair A X F) G)
      (presentedPerfectDGRightTensorIterated A D E T) =
    DGFunctor.comp (cubicalLambdaFunctorPair A X (cubicalLambdaFunctorPair A F G))
      (presentedPerfectDGRightTensorCompositeInner A D E T)
  rw [presentedPerfectDGRightTensorAction_comp]
  change DGFunctor.comp (cubicalLambdaFunctorPair A (cubicalLambdaFunctorPair A X F) G)
      (DGFunctor.comp (dgTensorAssociator A (PresentedPerfectDGObject A D) (DGFunctor A D E)
        (DGFunctor A E T)) (presentedPerfectDGRightTensorCompositeInner A D E T)) = _
  rw [← strictDGFunctor_comp_assoc, cubicalLambdaFunctorPair_associativity]

end SerrePositivity.KST.SConstruction
