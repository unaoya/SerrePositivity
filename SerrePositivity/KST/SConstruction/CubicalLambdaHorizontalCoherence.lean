module
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalDGAssociativity
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalDGUnits
public import SerrePositivity.KST.SConstruction.CubicalLambdaFunctorPairCoherence

/-! # Λ からの関手圏への実横合成の結合・単位
概要：同じ Λ からの実 dg 関手を Serre 対角で組にして横合成する操作の法則を示す。
方針：元の対角の結合・単位と、実 tensor dg 横合成の同じ全 Hom 等号を合成する。
規約：元の増大・閉単位・対象等号を保持。使われ方：native Kan 合成の全単体の法則。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D E B T : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A B] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} B]

/-- 同じ Λ からの三つの実関手族の横合成は、全 dg 関手として結合的。 -/
lemma cubicalLambdaHorizontal_associativity {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) (DGFunctor A D E))
    (G : DGFunctor A (CubicalLambda A K) (DGFunctor A E B))
    (H : DGFunctor A (CubicalLambda A K) (DGFunctor A B T)) :
    DGFunctor.comp
        (cubicalLambdaFunctorPair A
          (DGFunctor.comp (cubicalLambdaFunctorPair A F G) (dgFunctorHorizontalDG A D E B)) H)
        (dgFunctorHorizontalDG A D B T) =
      DGFunctor.comp
        (cubicalLambdaFunctorPair A F
          (DGFunctor.comp (cubicalLambdaFunctorPair A G H) (dgFunctorHorizontalDG A E B T)))
        (dgFunctorHorizontalDG A D E T) := by
  have hl := cubicalLambdaFunctorPair_post A (cubicalLambdaFunctorPair A F G) H
    (dgFunctorHorizontalDG A D E B) (DGFunctor.id (DGFunctor A B T))
  rw [strictDGFunctor_comp_id] at hl
  have hr := cubicalLambdaFunctorPair_post A F (cubicalLambdaFunctorPair A G H)
    (DGFunctor.id (DGFunctor A D E)) (dgFunctorHorizontalDG A E B T)
  rw [strictDGFunctor_comp_id] at hr
  rw [hl, hr, strictDGFunctor_comp_assoc, strictDGFunctor_comp_assoc]
  change DGFunctor.comp (cubicalLambdaFunctorPair A (cubicalLambdaFunctorPair A F G) H)
      (dgFunctorHorizontalLeftDG A D E B T) =
    DGFunctor.comp (cubicalLambdaFunctorPair A F (cubicalLambdaFunctorPair A G H))
      (dgFunctorHorizontalRightInnerDG A D E B T)
  rw [dgFunctorHorizontalDG_associativity]
  change DGFunctor.comp (cubicalLambdaFunctorPair A (cubicalLambdaFunctorPair A F G) H)
      (DGFunctor.comp (dgTensorAssociator A (DGFunctor A D E) (DGFunctor A E B)
        (DGFunctor A B T)) (dgFunctorHorizontalRightInnerDG A D E B T)) = _
  rw [← strictDGFunctor_comp_assoc, cubicalLambdaFunctorPair_associativity]

omit [DGCategory A B] [DGCategory A T] [Small.{u} B] [Small.{u} E] in
/-- 同じ Λ の元の増大から恒等関手を選んで左横合成すると、元の実関手族を回収。 -/
lemma cubicalLambdaHorizontal_left_unit {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) (DGFunctor A D E)) :
    DGFunctor.comp
        (cubicalLambdaFunctorPair A
          (DGFunctor.comp (cubicalLambdaCounit A K) (dgFunctorIdentityPoint A D)) F)
        (dgFunctorHorizontalDG A D D E) = F := by
  have h := cubicalLambdaFunctorPair_post A (cubicalLambdaCounit A K) F
    (dgFunctorIdentityPoint A D) (DGFunctor.id (DGFunctor A D E))
  rw [strictDGFunctor_comp_id] at h
  rw [h, strictDGFunctor_comp_assoc]
  change DGFunctor.comp (cubicalLambdaFunctorPair A (cubicalLambdaCounit A K) F)
      (dgFunctorHorizontalLeftUnitDG A D E) = F
  rw [dgFunctorHorizontalDG_left_unit, cubicalLambdaFunctorPair_left_unit]

omit [DGCategory A B] [DGCategory A T] [Small.{u} B] in
/-- 同じ Λ の元の増大から恒等関手を選んで右横合成すると、元の実関手族を回収。 -/
lemma cubicalLambdaHorizontal_right_unit {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) (DGFunctor A D E)) :
    DGFunctor.comp
        (cubicalLambdaFunctorPair A F
          (DGFunctor.comp (cubicalLambdaCounit A K) (dgFunctorIdentityPoint A E)))
        (dgFunctorHorizontalDG A D E E) = F := by
  have h := cubicalLambdaFunctorPair_post A F (cubicalLambdaCounit A K)
    (DGFunctor.id (DGFunctor A D E)) (dgFunctorIdentityPoint A E)
  rw [strictDGFunctor_comp_id] at h
  rw [h, strictDGFunctor_comp_assoc]
  change DGFunctor.comp (cubicalLambdaFunctorPair A F (cubicalLambdaCounit A K))
      (dgFunctorHorizontalRightUnitDG A D E) = F
  rw [dgFunctorHorizontalDG_right_unit, cubicalLambdaFunctorPair_right_unit]

end SerrePositivity.KST.SConstruction
