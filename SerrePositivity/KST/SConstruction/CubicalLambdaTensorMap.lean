module
public import SerrePositivity.KST.SConstruction.CubicalLambdaDiagonal
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-! # Λ の元の二射影による oplax tensor の実 dg 関手
概要：元の Serre 対角と全入力作用から、Λ(K×L) を実 dg tensor ΛK⊗ΛL へ送る。
方針：対角 dg 関手と元の二つの入力 dg 関手の tensor を合成する。
規約：Hom は元の対角に続く二つの射の tensor。使われ方：Prop.4.6 の全法則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj
variable (A : Type u) [CommRing A]

/-- 元の二つの単体的写像を、同じ Serre 対角によって実 dg tensor へ束ねる。 -/
def cubicalLambdaTensorPair {M K L : SSet.{u}} (a : M ⟶ K) (b : M ⟶ L) :
    DGFunctor A (CubicalLambda A M) (DGTensorCategory A (CubicalLambda A K) (CubicalLambda A L)) :=
  (cubicalLambdaDiagonal A M).comp (dgTensorFunctor A (cubicalLambdaMap A a) (cubicalLambdaMap A b))

/-- 元の二入力を束ねる対象作用は、元の零単体への二つの作用そのもの。 -/
lemma cubicalLambdaTensorPair_obj {M K L : SSet.{u}} (a : M ⟶ K) (b : M ⟶ L)
    (x : CubicalLambda A M) : (cubicalLambdaTensorPair A a b).obj x =
      ((cubicalLambdaMap A a).obj x, (cubicalLambdaMap A b).obj x) := rfl

/-- 束ねた Hom 作用は元の Serre 対角に続く元の二つの Hom 作用の tensor。 -/
lemma cubicalLambdaTensorPair_map {M K L : SSet.{u}} (a : M ⟶ K) (b : M ⟶ L)
    (x y : CubicalLambda A M) :
    (cubicalLambdaTensorPair A a b).map x y = Δ[x ⟶[Complex A] y] ≫
      ((cubicalLambdaMap A a).map x y ⊗ₘ (cubicalLambdaMap A b).map x y) := rfl

/-- 元の単体的直積の両射影による、Prop.4.6 の実 oplax tensor 成分。 -/
def cubicalLambdaOplaxTensor (K L : SSet.{u}) :
    DGFunctor A (CubicalLambda A (K ⨯ L))
      (DGTensorCategory A (CubicalLambda A K) (CubicalLambda A L)) :=
  cubicalLambdaTensorPair A prod.fst prod.snd

/-- Oplax tensor の対象作用は、元の単体的直積の両射影そのもの。 -/
lemma cubicalLambdaOplaxTensor_obj (K L : SSet.{u}) (x : CubicalLambda A (K ⨯ L)) :
    (cubicalLambdaOplaxTensor A K L).obj x =
      ((prod.fst : K ⨯ L ⟶ K).app _ x, (prod.snd : K ⨯ L ⟶ L).app _ x) := rfl

/-- Oplax tensor の Hom 作用は、元の Serre 対角と両射影の鎖写像の tensor。 -/
lemma cubicalLambdaOplaxTensor_map (K L : SSet.{u}) (x y : CubicalLambda A (K ⨯ L)) :
    (cubicalLambdaOplaxTensor A K L).map x y = Δ[x ⟶[Complex A] y] ≫
      ((cubicalLambdaMap A prod.fst).map x y ⊗ₘ (cubicalLambdaMap A prod.snd).map x y) := rfl

end SerrePositivity.KST.SConstruction
