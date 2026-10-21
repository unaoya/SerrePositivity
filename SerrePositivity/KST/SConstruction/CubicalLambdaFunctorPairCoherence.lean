module
public import SerrePositivity.KST.SConstruction.ComonoidFunctorPairLaws
public import SerrePositivity.KST.SConstruction.CubicalLambdaFunctorPair
public import SerrePositivity.KST.SConstruction.CubicalLambdaCounit
public import SerrePositivity.KST.SConstruction.DGTensorAssociator
public import SerrePositivity.KST.SConstruction.DGTensorUnitors

/-! # 元の Λ からの実 dg 関手の組の結合・単位則
概要：任意の実 dg 関手を Serre 対角で組にする操作の結合・左右単位を示す。
方針：元の全 Hom の余モノイド則を、任意出力への三つの射に適用する。
規約：対象と全 Hom の厳密等号。使われ方：native tensor 比較の結合・単位。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w} {B : Type z}
  [DGCategory A D] [DGCategory A E] [DGCategory A B]

/-- 元の Λ からの三実 dg 関手の組は、実 tensor の結合 dg 関手で一致する。 -/
lemma cubicalLambdaFunctorPair_associativity {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) D) (G : DGFunctor A (CubicalLambda A K) E)
    (H : DGFunctor A (CubicalLambda A K) B) :
    DGFunctor.comp (cubicalLambdaFunctorPair A (cubicalLambdaFunctorPair A F G) H)
        (dgTensorAssociator A D E B) =
      cubicalLambdaFunctorPair A F (cubicalLambdaFunctorPair A G H) := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (comonoidFunctorPair_associativity
    (cubicalLambdaHomComonoid A K x y) (F.map x y) (G.map x y) (H.map x y))

/-- 左出力が元の増大なら、実左単位 dg 関手は元の右出力を回収する。 -/
lemma cubicalLambdaFunctorPair_left_unit {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) D) :
    DGFunctor.comp (cubicalLambdaFunctorPair A (cubicalLambdaCounit A K) F)
        (dgTensorLeftUnitor A D) = F := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans
    (comonoidFunctorPair_left_unit (cubicalLambdaHomComonoid A K x y) (F.map x y))

/-- 右出力が元の増大なら、実右単位 dg 関手は元の左出力を回収する。 -/
lemma cubicalLambdaFunctorPair_right_unit {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) D) :
    DGFunctor.comp (cubicalLambdaFunctorPair A F (cubicalLambdaCounit A K))
        (dgTensorRightUnitor A D) = F := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans
    (comonoidFunctorPair_right_unit (cubicalLambdaHomComonoid A K x y) (F.map x y))

end SerrePositivity.KST.SConstruction
