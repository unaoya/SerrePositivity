module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingValues

/-!
概要：barの同じ退化部分への元のlatching余錐は、実際の余極限である。
方針：被覆する脚の任意の表示から値を取り、全表示での一致で自然性と一意性を示す。
規約：元の全係数と全てのlatchingの脚を保つ。
使われ方：IS-W2 R03f.2の相対latchingの退化・非退化による分離。
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

/-- 退化行の各単体に、元の余錐の全ての表示で一致する値がある。 -/
theorem simplicialReplacementRowLatching_exists_value
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    ∃ v : c.pt.obj q, ∀ (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
      (x : ((simplicialReplacementRows F).obj j.obj.left).obj q),
      (simplicialReplacementRowLatchingLeg F n j).app q x = s → (c.ι.app j).app q x = v := by
  obtain ⟨j,x,hj⟩ := simplicialReplacementRowLatching_jointly_surjective F n q s
  refine ⟨(c.ι.app j).app q x, ?_⟩
  intro k y hk
  exact simplicialReplacementRowLatching_values_eq F n c q k j y x (hk.trans hj.symm)

/-- 元の全ての表示で一致する同じ退化単体の値。 -/
def simplicialReplacementRowLatchingValue
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    c.pt.obj q := (simplicialReplacementRowLatching_exists_value F n c q s).choose

/-- 指定された元の脚上では、選んだ値はその同じ余錐の値に厳密に一致する。 -/
theorem simplicialReplacementRowLatchingValue_fac
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q) :
    simplicialReplacementRowLatchingValue F n c q
      ((simplicialReplacementRowLatchingLeg F n j).app q x) = (c.ι.app j).app q x :=
  ((simplicialReplacementRowLatching_exists_value F n c q _).choose_spec j x rfl).symm

/-- 任意の元の余錐へ、同じ退化部分から自然に降下する。 -/
def simplicialReplacementRowLatchingDesc
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F)) :
    (simplicialReplacementDegenerateRow F n : SSet.{u}) ⟶ c.pt where
  app q := ↾simplicialReplacementRowLatchingValue F n c q
  naturality q r α := by
    apply ConcreteCategory.hom_ext
    intro s
    obtain ⟨j,x,rfl⟩ := simplicialReplacementRowLatching_jointly_surjective F n q s
    have hn := ConcreteCategory.congr_hom
      ((simplicialReplacementRowLatchingLeg F n j).naturality α) x
    change (simplicialReplacementRowLatchingLeg F n j).app r
      (((simplicialReplacementRows F).obj j.obj.left).map α x) =
        (simplicialReplacementDegenerateRow F n : SSet.{u}).map α
          ((simplicialReplacementRowLatchingLeg F n j).app q x) at hn
    change simplicialReplacementRowLatchingValue F n c r
      ((simplicialReplacementDegenerateRow F n : SSet.{u}).map α
        ((simplicialReplacementRowLatchingLeg F n j).app q x)) =
      c.pt.map α (simplicialReplacementRowLatchingValue F n c q
        ((simplicialReplacementRowLatchingLeg F n j).app q x))
    rw [← hn, simplicialReplacementRowLatchingValue_fac, simplicialReplacementRowLatchingValue_fac]
    exact ConcreteCategory.congr_hom ((c.ι.app j).naturality α) x

/-- 同じ退化部分への元のlatching余錐は、全係数を保つ実際の余極限である。 -/
def simplicialReplacementRowLatchingIsColimit :
    IsColimit (simplicialReplacementRowLatchingCocone F n) where
  desc := simplicialReplacementRowLatchingDesc F n
  fac c j := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    exact simplicialReplacementRowLatchingValue_fac F n c q j x
  uniq c m hm := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro s
    obtain ⟨j,x,rfl⟩ := simplicialReplacementRowLatching_jointly_surjective F n q s
    have h := ConcreteCategory.congr_hom (congr_app (hm j) q) x
    change m.app q ((simplicialReplacementRowLatchingLeg F n j).app q x) =
      (c.ι.app j).app q x at h
    exact h.trans (simplicialReplacementRowLatchingValue_fac F n c q j x).symm

/-- 実際のlatchingの余極限は、元の同じ退化部分と同型。 -/
def simplicialReplacementRowLatchingIso :
    colimit (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) ≅
      simplicialReplacementDegenerateRow F n :=
  (colimit.isColimit _).coconePointUniqueUpToIso (simplicialReplacementRowLatchingIsColimit F n)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
