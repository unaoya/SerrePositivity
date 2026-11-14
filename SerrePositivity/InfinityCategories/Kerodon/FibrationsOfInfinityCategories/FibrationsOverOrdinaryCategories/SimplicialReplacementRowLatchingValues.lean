module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingRefinement

/-!
概要：元のlatching余錐の同じ退化単体の二表示は、任意の余錐で同じ値を持つ。
方針：同じ非退化表示へ係数ごと戻し、退化の単射性と余錐の自然性を使う。
規約：任意の単体次数、元の係数、元の余錐の全ての脚を保つ。
使われ方：IS-W2 R03f.2の退化行の余極限性。
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

/-- 元の余錐の自然性は、元のlatchingの射に沿って同じ係数の値を保つ。 -/
theorem simplicialReplacementRowLatching_value_map
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) {j k : LatchingIndex simplexOp (Opposite.op ⦋n⦌)} (f : j ⟶ k)
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (y : ((simplicialReplacementRows F).obj k.obj.left).obj q)
    (h : ((simplicialReplacementRows F).map f.hom.left).app q x = y) :
    (c.ι.app j).app q x = (c.ι.app k).app q y := by
  have hc := ConcreteCategory.congr_hom (congr_app (c.w f) q) x
  change (c.ι.app k).app q (((simplicialReplacementRows F).map f.hom.left).app q x) =
    (c.ι.app j).app q x at hc
  rw [h] at hc
  exact hc.symm

/-- 同じ元の退化単体の二つのlatching表示は、任意の元の余錐で同じ値になる。 -/
theorem simplicialReplacementRowLatching_values_eq
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (j k : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (y : ((simplicialReplacementRows F).obj k.obj.left).obj q)
    (h : (simplicialReplacementRowLatchingLeg F n j).app q x =
      (simplicialReplacementRowLatchingLeg F n k).app q y) :
    (c.ι.app j).app q x = (c.ι.app k).app q y := by
  let z := (simplicialReplacementRowLatchingLeg F n j).app q x
  obtain ⟨m, hm, α, hα, τ, hτ⟩ :=
    simplicialReplacement_degenerate_presentation z.val.1 z.property
  haveI : Epi α := hα
  have hj : (nerve I).map α.op τ = (((simplicialReplacementRows F).map j.obj.hom).app q x).1 :=
    hτ.symm
  have hk : (nerve I).map α.op τ = (((simplicialReplacementRows F).map k.obj.hom).app q y).1 :=
    hτ.symm.trans (congrArg (fun w => w.val.1) h)
  obtain ⟨fj, vj, hj'⟩ := simplicialReplacementRowLatching_refine F q hm α τ j x hj
  obtain ⟨fk, vk, hk'⟩ := simplicialReplacementRowLatching_refine F q hm α τ k y hk
  let a := simplicialReplacementLatchingIndexOfEpi hm α
  let u : (simplicialReplacementRow F m).obj q := ⟨τ.val,vj⟩
  let v : (simplicialReplacementRow F m).obj q := ⟨τ.val,vk⟩
  have hu := simplicialReplacementRowLatching_value_map F n
    (simplicialReplacementRowLatchingCocone F n) q fj u x hj'
  have hv := simplicialReplacementRowLatching_value_map F n
    (simplicialReplacementRowLatchingCocone F n) q fk v y hk'
  have he : (simplicialReplacementRowReindex F α).app q u =
      (simplicialReplacementRowReindex F α).app q v :=
    congrArg Subtype.val (hu.trans (h.trans hv.symm))
  haveI : Mono (simplicialReplacementRowReindex F α) := simplicialReplacementRowReindex_mono F α
  have huv : u = v := (CategoryTheory.mono_iff_injective
    ((simplicialReplacementRowReindex F α).app q)).mp inferInstance he
  exact (simplicialReplacementRowLatching_value_map F n c q fj u x hj').symm.trans
    ((congrArg (fun w => (c.ι.app a).app q w) huv).trans
      (simplicialReplacementRowLatching_value_map F n c q fk v y hk'))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
