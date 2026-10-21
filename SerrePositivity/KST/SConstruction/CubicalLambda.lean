module
public import SerrePositivity.KST.SConstruction.CubicalRigidification
public import SerrePositivity.KST.SConstruction.EnrichedFunctorTransport
public import SerrePositivity.KST.SConstruction.CubicalSerreDayMonoidal
public import SerrePositivity.DifferentialGraded.Category.Basic

/-! # 元の cubical rigidification の Serre 鎖による Λ
概要：元の零単体と全 necklace の cubical mapping object の鎖から Λ を構成する。
方針：元の強モノイダル Serre 鎖関手で実豊穣圏と実豊穣関手を移送する。
規約：全 Hom・単位・合成を回収する。使われ方：Λ の oplax tensor と dg nerve 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の cubical rigidification に Serre 鎖を施した dg 圏 Λ。 -/
abbrev CubicalLambda (K : SSet.{u}) : Type u :=
  TransportEnrichment (cubicalDaySerreChains A) (CubicalRigidification K)

/-- Λ は元の mapping object の鎖を Hom とする実 dg 圏。 -/
instance cubicalLambdaDGCategory (K : SSet.{u}) : DGCategory A (CubicalLambda A K) :=
  inferInstanceAs (EnrichedCategory (Complex A)
    (TransportEnrichment (cubicalDaySerreChains A) (CubicalRigidification K)))

/-- Λ の対象は元の単体集合の零単体と同じ。 -/
def cubicalLambdaVertexEquiv (K : SSet.{u}) : CubicalLambda A K ≃ K _⦋0⦌ :=
  Equiv.refl _

/-- Λ の Hom 複体は、元の全 necklace の mapping object の Serre 鎖そのもの。 -/
lemma cubicalLambda_hom (K : SSet.{u}) (x y : CubicalLambda A K) :
    (x ⟶[Complex A] y) = (cubicalSerreChains A).obj (necklaceCubicalMapping K x y) := rfl

/-- Λ の単位は元の一点の単位射を Serre 鎖に送ったもの。 -/
lemma cubicalLambda_id (K : SSet.{u}) (x : CubicalLambda A K) :
    eId (Complex A) x = Functor.LaxMonoidal.ε (cubicalDaySerreChains A) ≫
      (cubicalDaySerreChains A).map (necklaceCubicalDayIdentity K x) := rfl

/-- Λ の合成は元の Day 合成を、元の Serre tensor 比較で鎖へ移したもの。 -/
lemma cubicalLambda_comp (K : SSet.{u}) (x y z : CubicalLambda A K) :
    eComp (Complex A) x y z =
      Functor.LaxMonoidal.μ (cubicalDaySerreChains A)
        (necklaceCubicalDayMapping K x y) (necklaceCubicalDayMapping K y z) ≫
        (cubicalDaySerreChains A).map (necklaceCubicalDayCompose K x y z) := rfl

/-- 元の全単体的写像は、Λ の実 dg 関手を定める。 -/
def cubicalLambdaMap {K L : SSet.{u}} (a : K ⟶ L) :
    EnrichedFunctor (Complex A) (CubicalLambda A K) (CubicalLambda A L) :=
  enrichedFunctorTransport (cubicalDaySerreChains A) (cubicalRigidificationMap a)

/-- Λ の入力関手の対象作用は元の零単体への作用そのもの。 -/
lemma cubicalLambdaMap_obj {K L : SSet.{u}} (a : K ⟶ L) (x : CubicalLambda A K) :
    (cubicalLambdaMap A a).obj x = a.app _ x := rfl

/-- Λ の入力関手の Hom 作用は元の全 necklace の余極限の写像の Serre 鎖。 -/
lemma cubicalLambdaMap_map {K L : SSet.{u}} (a : K ⟶ L) (x y : CubicalLambda A K) :
    (cubicalLambdaMap A a).map x y =
      (cubicalSerreChains A).map (necklaceCubicalMap a x y) := rfl

/-- Λ は元の恒等入力を実 dg 関手の恒等へ厳密に送る。 -/
lemma cubicalLambdaMap_id (K : SSet.{u}) :
    cubicalLambdaMap A (𝟙 K) = EnrichedFunctor.id (Complex A) (CubicalLambda A K) :=
  (congrArg (enrichedFunctorTransport (cubicalDaySerreChains A))
    (cubicalRigidificationMap_id K)).trans
      (enrichedFunctorTransport_id (cubicalDaySerreChains A))

/-- Λ は元の入力の合成を実 dg 関手の合成へ厳密に送る。 -/
lemma cubicalLambdaMap_comp {K L M : SSet.{u}} (a : K ⟶ L) (b : L ⟶ M) :
    cubicalLambdaMap A (a ≫ b) =
      EnrichedFunctor.comp (Complex A) (cubicalLambdaMap A a) (cubicalLambdaMap A b) :=
  (congrArg (enrichedFunctorTransport (cubicalDaySerreChains A))
    (cubicalRigidificationMap_comp a b)).trans
      (enrichedFunctorTransport_comp (cubicalDaySerreChains A)
        (cubicalRigidificationMap a) (cubicalRigidificationMap b))

end SerrePositivity.KST.SConstruction
