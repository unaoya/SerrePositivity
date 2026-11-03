module
public import SerrePositivity.KST.SConstruction.CubicalLambdaComonoids
public import SerrePositivity.KST.SConstruction.ComonoidTensorDiagonal
public import SerrePositivity.KST.SConstruction.DGTensorFunctor
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # Λ の元の Serre 対角による実 dg 関手
概要：各 Hom の元の Serre 対角を、Λ から実 dg tensor への関手へ束ねる。
方針：元の単位・合成が余モノイド射であることから、二つの dg 関手則を得る。
規約：tensor の中央二因子の signed 交換を保持。使われ方：Λ の oplax tensor。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj
variable (A : Type u) [CommRing A]

/-- 元の Serre 対角は、元の Λ の単位を保つ。 -/
lemma cubicalLambdaDiagonal_identity (K : SSet.{u}) (x : CubicalLambda A K) :
    eId (Complex A) x ≫ Δ[x ⟶[Complex A] x] =
      eId (Complex A) (show DGTensorCategory A (CubicalLambda A K) (CubicalLambda A K)
        from (x, x)) :=
  (cubicalLambdaIdentityComonoid A K x).isComonHom_hom.hom_comul

/-- 元の Serre 対角は、中央二因子の交換を持つ実 dg tensor の合成を保つ。 -/
lemma cubicalLambdaDiagonal_composition (K : SSet.{u}) (x y z : CubicalLambda A K) :
    eComp (Complex A) x y z ≫ Δ[x ⟶[Complex A] z] =
      (Δ[x ⟶[Complex A] y] ⊗ₘ Δ[y ⟶[Complex A] z]) ≫
        eComp (Complex A)
          (show DGTensorCategory A (CubicalLambda A K) (CubicalLambda A K) from (x, x))
          (show DGTensorCategory A (CubicalLambda A K) (CubicalLambda A K) from (y, y))
          (show DGTensorCategory A (CubicalLambda A K) (CubicalLambda A K) from (z, z)) := by
  have h := comonoidTensorDiagonal (cubicalLambdaComposeComonoid A K x y z)
  have ht := dgTensor_composition A (CubicalLambda A K) (CubicalLambda A K)
    (x, x) (y, y) (z, z)
  exact h.trans
    (congrArg (fun b => (Δ[x ⟶[Complex A] y] ⊗ₘ Δ[y ⟶[Complex A] z]) ≫ b) ht.symm)

/-- 元の Serre 対角は、Λ から二つの同じ Λ の実 dg tensor への dg 関手を定める。 -/
def cubicalLambdaDiagonal (K : SSet.{u}) :
    DGFunctor A (CubicalLambda A K)
      (DGTensorCategory A (CubicalLambda A K) (CubicalLambda A K)) where
  obj x := (x, x)
  map x y := Δ[x ⟶[Complex A] y]
  map_id x := cubicalLambdaDiagonal_identity A K x
  map_comp x y z := cubicalLambdaDiagonal_composition A K x y z

/-- 元の対角関手は対象を同じ二対象へ送る。 -/
lemma cubicalLambdaDiagonal_obj (K : SSet.{u}) (x : CubicalLambda A K) :
    (cubicalLambdaDiagonal A K).obj x = (x, x) := rfl

/-- 元の対角関手の Hom 作用は元の Serre 対角そのもの。 -/
lemma cubicalLambdaDiagonal_map (K : SSet.{u}) (x y : CubicalLambda A K) :
    (cubicalLambdaDiagonal A K).map x y = Δ[x ⟶[Complex A] y] := rfl

/-- 元の全入力写像は、元の対角関手と実 dg tensor への作用を厳密に可換にする。 -/
lemma cubicalLambdaDiagonal_naturality {K L : SSet.{u}} (a : K ⟶ L) :
    DGFunctor.comp (cubicalLambdaMap A a) (cubicalLambdaDiagonal A L) =
      DGFunctor.comp (cubicalLambdaDiagonal A K)
        (dgTensorFunctor A (cubicalLambdaMap A a) (cubicalLambdaMap A a)) := by
  refine EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (cubicalLambdaMap A a) (cubicalLambdaDiagonal A L))
    (G := DGFunctor.comp (cubicalLambdaDiagonal A K)
      (dgTensorFunctor A (cubicalLambdaMap A a) (cubicalLambdaMap A a))) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans
    (cubicalLambdaMapComonoid A a x y).isComonHom_hom.hom_comul

end SerrePositivity.KST.SConstruction
