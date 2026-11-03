module
public import SerrePositivity.KST.SConstruction.CubicalLambdaDiagonal
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Λ の元の Serre 増大による実 dg 関手
概要：元の全 Hom の Serre 増大を、一対象 A の dg 圏への実 dg 関手に束ねる。
方針：元の単位・合成の余モノイド射としての増大保存を使う。
規約：元の増大と入力自然性を保持。使われ方：Λ の oplax 単位と単位則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj
variable (A : Type u) [CommRing A]

/-- 元の Serre 増大は、Λ から一対象 A の dg 圏への実 dg 関手を定める。 -/
def cubicalLambdaCounit (K : SSet.{u}) : DGFunctor A (CubicalLambda A K) PUnit where
  obj _ := PUnit.unit
  map x y := ε[x ⟶[Complex A] y]
  map_id x := (cubicalLambdaIdentityComonoid A K x).isComonHom_hom.hom_counit
  map_comp x y z := comonoidTensorCounit (cubicalLambdaComposeComonoid A K x y z)

/-- 元の増大 dg 関手の全 Hom 作用は、元の Serre 増大そのもの。 -/
lemma cubicalLambdaCounit_map (K : SSet.{u}) (x y : CubicalLambda A K) :
    (cubicalLambdaCounit A K).map x y = ε[x ⟶[Complex A] y] := rfl

/-- 元の増大 dg 関手は、全入力写像について厳密に自然。 -/
lemma cubicalLambdaCounit_naturality {K L : SSet.{u}} (a : K ⟶ L) :
    DGFunctor.comp (cubicalLambdaMap A a) (cubicalLambdaCounit A L) =
      cubicalLambdaCounit A K := by
  refine EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (cubicalLambdaMap A a) (cubicalLambdaCounit A L))
    (G := cubicalLambdaCounit A K) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans
    (cubicalLambdaMapComonoid A a x y).isComonHom_hom.hom_counit

/-- 元の終対象の Λ から一対象 A の dg 圏への実 oplax 単位成分。 -/
def cubicalLambdaOplaxUnit : DGFunctor A (CubicalLambda A (⊤_ SSet.{u})) PUnit :=
  cubicalLambdaCounit A _

/-- 元の各 Hom で、対角と左の増大は元の左単位を通して恒等を回収する。 -/
lemma cubicalLambdaDiagonal_left_counit (K : SSet.{u}) (x y : CubicalLambda A K) :
    ((cubicalLambdaDiagonal A K).map x y ≫
      ((cubicalLambdaCounit A K).map x y ⊗ₘ 𝟙 (x ⟶[Complex A] y))) ≫
        (λ_ (x ⟶[Complex A] y)).hom = 𝟙 (x ⟶[Complex A] y) :=
  comonoidDiagonal_left_counit (cubicalLambdaHomComonoid A K x y)

/-- 元の各 Hom で、対角と右の増大は元の右単位を通して恒等を回収する。 -/
lemma cubicalLambdaDiagonal_right_counit (K : SSet.{u}) (x y : CubicalLambda A K) :
    ((cubicalLambdaDiagonal A K).map x y ≫
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ (cubicalLambdaCounit A K).map x y)) ≫
        (ρ_ (x ⟶[Complex A] y)).hom = 𝟙 (x ⟶[Complex A] y) :=
  comonoidDiagonal_right_counit (cubicalLambdaHomComonoid A K x y)

end SerrePositivity.KST.SConstruction
