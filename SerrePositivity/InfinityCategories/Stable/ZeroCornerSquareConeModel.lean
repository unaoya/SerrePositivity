module
public import SerrePositivity.InfinityCategories.Stable.ConeInputFullSubcomplex
public import SerrePositivity.InfinityCategories.Stable.ZeroOuterCospans

/-!
概要：零隅四角形と同じ cospan 上の錐の実比較。
方針：全部分複体・引き戻し・形状同型を全単体で照合する。
規約：安定性・余極限は先取りしない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ実図式の比較 `IsZeroCornerSquareVertex`。 -/
def IsZeroCornerSquareVertex {X : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  IsZeroVertex (squareVertex (squareDiagram v) 1 0) ∧
    IsZeroVertex (squareVertex (squareDiagram v) 0 1)
/-- 同じ実図式の比較 `zeroCornerSquares`。 -/
def zeroCornerSquares (X : SSet.{u}) : SSet.{u} :=
  (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    IsZeroCornerSquareVertex : SSet.{u})
/-- 同じ実図式の比較 `squareConeFunctorIso`。 -/
def squareConeFunctorIso (X : SSet.{u}) :
    (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X ≅
      (ihom (join (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}))).obj X where
  hom := (pre cospanConeSquareIso.hom).app X
  inv := (pre cospanConeSquareIso.inv).app X
  hom_inv_id := by
    simp only [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id, NatTrans.id_app]
  inv_hom_id := by
    simp only [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id, NatTrans.id_app]

/-- 同じ実図式の比較 `zeroCornerSquareConeIso`。 -/
def zeroCornerSquareConeIso (X : SSet.{u}) :
    zeroCornerSquares X ≅
      pullback (coneRestriction (horn 2 2 : SSet.{u}) X)
        (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          IsZeroOuterCospanVertex).ι := by
  let P := fun v ↦ IsZeroOuterCospanVertex
    ((coneRestriction (horn 2 2 : SSet.{u}) X).app (Opposite.op ⦋0⦌) v)
  refine fullSubcomplexIso (squareConeFunctorIso X) IsZeroCornerSquareVertex P ?_ ≪≫
    coneInputFullSubcomplexIso _ _
  intro v
  change IsZeroCornerSquareVertex v ↔ IsZeroOuterCospanVertex
    (((pre cospanConeSquareIso.hom).app X ≫
      coneRestriction (horn 2 2 : SSet.{u}) X).app (Opposite.op ⦋0⦌) v)
  change IsZeroCornerSquareVertex v ↔ IsZeroOuterCospanVertex
    (((pre cospanConeSquareIso.hom).app X ≫
      (pre (joinInr (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}))).app X).app
      (Opposite.op ⦋0⦌) v)
  rw [← NatTrans.comp_app, ← pre_map]
  exact (zeroOuterCospanVertex_square_iff v).symm
end SerrePositivity.InfinityCategories
