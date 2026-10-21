module
public import SerrePositivity.KST.SConstruction.CubicalLambdaDiagonal

/-! # 元の Λ 対角による二つの実 dg 関手の組
概要：共通の Λ を源とする二つの dg 関手を、実 tensor dg 圏への関手にする。
方針：元の Serre 対角の後で二つの Hom 作用を tensor する。
規約：因子順と全次数を保持。使われ方：native dg nerve の直積から tensor への比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- 同じ元の Λ からの二関手を、元の Serre 対角で実 tensor へ組にする。 -/
def cubicalLambdaFunctorPair {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) D) (G : DGFunctor A (CubicalLambda A K) E) :
    DGFunctor A (CubicalLambda A K) (DGTensorCategory A D E) :=
  DGFunctor.comp (cubicalLambdaDiagonal A K) (dgTensorFunctor A F G)

/-- 実 tensor への組の対象作用は、元の二つの対象作用の組。 -/
lemma cubicalLambdaFunctorPair_obj {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) D) (G : DGFunctor A (CubicalLambda A K) E)
    (x : CubicalLambda A K) :
    (cubicalLambdaFunctorPair A F G).obj x = (F.obj x, G.obj x) := rfl

/-- 実 tensor への組の全 Hom 作用は、元の対角と二つの Hom 作用の tensor。 -/
lemma cubicalLambdaFunctorPair_map {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) D) (G : DGFunctor A (CubicalLambda A K) E)
    (x y : CubicalLambda A K) :
    (cubicalLambdaFunctorPair A F G).map x y =
      Δ[x ⟶[Complex A] y] ≫ (F.map x y ⊗ₘ G.map x y) := rfl

/-- 全入力前合成は、元の対角による二関手の組と厳密に可換。 -/
lemma cubicalLambdaFunctorPair_precompose {K L : SSet.{u}} (a : K ⟶ L)
    (F : DGFunctor A (CubicalLambda A L) D) (G : DGFunctor A (CubicalLambda A L) E) :
    cubicalLambdaFunctorPair A (DGFunctor.comp (cubicalLambdaMap A a) F)
        (DGFunctor.comp (cubicalLambdaMap A a) G) =
      DGFunctor.comp (cubicalLambdaMap A a) (cubicalLambdaFunctorPair A F G) := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  apply (Category.comp_id _).trans
  change Δ[x ⟶[Complex A] y] ≫
      (((cubicalLambdaMap A a).map x y ≫ F.map _ _) ⊗ₘ
        ((cubicalLambdaMap A a).map x y ≫ G.map _ _)) =
    (cubicalLambdaMap A a).map x y ≫
      (Δ[(cubicalLambdaMap A a).obj x ⟶[Complex A] (cubicalLambdaMap A a).obj y] ≫
      (F.map _ _ ⊗ₘ G.map _ _))
  have h : (cubicalLambdaMap A a).map x y ≫
      Δ[(cubicalLambdaMap A a).obj x ⟶[Complex A] (cubicalLambdaMap A a).obj y] =
      Δ[x ⟶[Complex A] y] ≫
        ((cubicalLambdaMap A a).map x y ⊗ₘ (cubicalLambdaMap A a).map x y) :=
    (cubicalLambdaMapComonoid A a x y).isComonHom_hom.hom_comul
  rw [← tensorHom_comp_tensorHom, ← Category.assoc, ← h, Category.assoc]

/-- 二つの厳密 dg 後合成は、元の Serre 対角による組と厳密に可換。 -/
lemma cubicalLambdaFunctorPair_post {K : SSet.{u}} {B : Type v} {C : Type w}
    [DGCategory A B] [DGCategory A C]
    (F : DGFunctor A (CubicalLambda A K) D) (G : DGFunctor A (CubicalLambda A K) E)
    (H : DGFunctor A D B) (I : DGFunctor A E C) :
    cubicalLambdaFunctorPair A (DGFunctor.comp F H) (DGFunctor.comp G I) =
      DGFunctor.comp (cubicalLambdaFunctorPair A F G) (dgTensorFunctor A H I) := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  apply (Category.comp_id _).trans
  change Δ[x ⟶[Complex A] y] ≫
      ((F.map x y ≫ H.map _ _) ⊗ₘ (G.map x y ≫ I.map _ _)) =
    (Δ[x ⟶[Complex A] y] ≫ (F.map x y ⊗ₘ G.map x y)) ≫ (H.map _ _ ⊗ₘ I.map _ _)
  rw [← tensorHom_comp_tensorHom, Category.assoc]

end SerrePositivity.KST.SConstruction
