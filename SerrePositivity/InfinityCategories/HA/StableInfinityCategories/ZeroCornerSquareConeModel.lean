module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ConeInputFullSubcomplex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroOuterCospans

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ実図式の比較 `IsZeroCornerSquareVertex`。 -/
def IsZeroCornerSquareVertex {X : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v) 1 0) ∧
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v) 0 1)
/-- 同じ実図式の比較 `zeroCornerSquares`。 -/
def zeroCornerSquares (X : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    IsZeroCornerSquareVertex : SSet.{u})
/-- 同じ実図式の比較 `squareConeFunctorIso`。 -/
def squareConeFunctorIso (X : SSet.{u}) :
    (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X ≅
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}))).obj X where
  hom := (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom).app X
  inv := (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv).app X
  hom_inv_id := by
    simp only [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id, NatTrans.id_app]
  inv_hom_id := by
    simp only [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id, NatTrans.id_app]

/-- 同じ実図式の比較 `zeroCornerSquareConeIso`。 -/
def zeroCornerSquareConeIso (X : SSet.{u}) :
    zeroCornerSquares X ≅
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι := by
  let P := fun v ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X).app (Opposite.op ⦋0⦌) v)
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (squareConeFunctorIso X) IsZeroCornerSquareVertex P ?_ ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneInputFullSubcomplexIso _ _
  intro v
  change IsZeroCornerSquareVertex v ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex
    (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom).app X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X).app (Opposite.op ⦋0⦌) v)
  change IsZeroCornerSquareVertex v ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex
    (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom).app X ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}))).app X).app
      (Opposite.op ⦋0⦌) v)
  rw [← NatTrans.comp_app, ← pre_map]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterCospanVertex_square_iff v).symm
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
