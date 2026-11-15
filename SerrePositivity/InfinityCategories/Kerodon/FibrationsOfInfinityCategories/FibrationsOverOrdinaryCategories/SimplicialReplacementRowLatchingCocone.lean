module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowParts
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLeftAnodyne

/-!
概要：barの外側のlatching図式から、同じ退化基底成分への余錐を作る。
方針：各真の退化作用素は、より低い次数の基底射列からの像であることを記録する。
規約：latchingとの同型性はここでは主張しない。元の全ての脚を保持する。
使われ方：IS-W2 R03f.2の退化部分と実際の相対latchingの同定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
open SerrePositivity.Reedy
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) (n : ℕ)

/-- 真の退化作用素の脚は、同じ基底の退化成分へ厳密に因子分解する。 -/
def simplicialReplacementRowLatchingLeg (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    (simplicialReplacementRows F).obj s.obj.left ⟶ simplicialReplacementDegenerateRow F n :=
  Subcomplex.lift ((simplicialReplacementRows F).map s.obj.hom) (by
    rintro q _ ⟨⟨σ,x⟩, rfl⟩
    refine ⟨s.obj.left.unop.len, latching_degree_lt simplexOp s, s.obj.hom.unop, σ, ?_⟩
    rfl)

/-- 同じ退化成分への脚の包含は、元の行の作用素そのものである。 -/
theorem simplicialReplacementRowLatchingLeg_inclusion
    (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    simplicialReplacementRowLatchingLeg F n s ≫ (simplicialReplacementDegenerateRow F n).ι =
      (simplicialReplacementRows F).map s.obj.hom := rfl

/-- 元の外側latching図式の、同じ退化成分への全余錐。 -/
def simplicialReplacementRowLatchingCocone :
    Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) where
  pt := simplicialReplacementDegenerateRow F n
  ι.app s := simplicialReplacementRowLatchingLeg F n s
  ι.naturality s t f := by
    change (simplicialReplacementRows F).map f.hom.left ≫
      simplicialReplacementRowLatchingLeg F n t = simplicialReplacementRowLatchingLeg F n s ≫ 𝟙 _
    rw [Category.comp_id]
    apply (cancel_mono (simplicialReplacementDegenerateRow F n).ι).mp
    rw [Category.assoc, simplicialReplacementRowLatchingLeg_inclusion,
      simplicialReplacementRowLatchingLeg_inclusion]
    change (simplicialReplacementRows F).map f.hom.left ≫
      (simplicialReplacementRows F).map t.obj.hom = _
    rw [← (simplicialReplacementRows F).map_comp, f.hom.w]

/-- 実際のlatchingの余極限から、同じ退化成分への比較射。 -/
def simplicialReplacementLatchingToDegenerate :
    colimit (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) ⟶
      simplicialReplacementDegenerateRow F n :=
  colimit.desc _ (simplicialReplacementRowLatchingCocone F n)

/-- 実際の比較射は、元の全てのlatchingの脚を厳密に回収する。 -/
theorem simplicialReplacementLatchingToDegenerate_fac
    (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    colimit.ι (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) s ≫
      simplicialReplacementLatchingToDegenerate F n = simplicialReplacementRowLatchingLeg F n s :=
  colimit.ι_desc (simplicialReplacementRowLatchingCocone F n) s

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
