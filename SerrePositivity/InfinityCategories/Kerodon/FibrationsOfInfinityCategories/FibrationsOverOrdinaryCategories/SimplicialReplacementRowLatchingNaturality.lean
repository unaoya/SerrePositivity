module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingColimit

/-!
概要：実際のlatchingと同じ退化部分の同型は、元の係数射と境界包含を保つ。
方針：全latchingの脚上で照合し、実際の余極限の一意性を使う。
規約：元のlatching評価関手と元の比較射そのものを使う。
使われ方：IS-W2 R03f.2の元の相対latchingから指定境界付き持ち上げへの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
open SerrePositivity.Reedy
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (n : ℕ)

/-- 元のlatchingの同型は、同じ元の全ての脚を持つ比較射そのものである。 -/
theorem simplicialReplacementRowLatchingIso_hom (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).hom = simplicialReplacementLatchingToDegenerate F n := rfl

/-- 同じlatching同型は、元の境界包含を厳密に回収する。 -/
theorem simplicialReplacementRowLatchingIso_inclusion (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).hom ≫ (simplicialReplacementDegenerateRow F n).ι =
      (latchingComparison simplexOp (Opposite.op ⦋n⦌)).app (simplicialReplacementRows F) := by
  change colimit.desc _ (simplicialReplacementRowLatchingCocone F n) ≫ _ =
    colimit.desc _ (latchingCocone simplexOp (simplicialReplacementRows F) (Opposite.op ⦋n⦌))
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_desc_assoc, colimit.ι_desc]
  exact simplicialReplacementRowLatchingLeg_inclusion F n j

/-- 元のlatchingの脚は、同じ係数射の制限と可換する。 -/
theorem simplicialReplacementRowLatchingLeg_map {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    simplicialReplacementRowMap η j.obj.left.unop.len ≫ simplicialReplacementRowLatchingLeg G n j =
      simplicialReplacementRowLatchingLeg F n j ≫
        simplicialReplacementRowPartMap η n ((nerve I).degenerate n) := by
  apply (cancel_mono (simplicialReplacementDegenerateRow G n).ι).mp
  rw [Category.assoc, simplicialReplacementRowLatchingLeg_inclusion, Category.assoc,
    simplicialReplacementRowPartMap_inclusion, ← Category.assoc,
    simplicialReplacementRowLatchingLeg_inclusion]
  exact ((simplicialReplacementRowsMap η).naturality j.obj.hom).symm

/-- 同じlatchingの全同型は、元の係数射に自然である。 -/
theorem simplicialReplacementRowLatchingIso_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    (latchingEvaluation simplexOp (Opposite.op ⦋n⦌)).map (simplicialReplacementRowsMap η) ≫
      (simplicialReplacementRowLatchingIso G n).hom =
    (simplicialReplacementRowLatchingIso F n).hom ≫
      simplicialReplacementRowPartMap η n ((nerve I).degenerate n) := by
  apply colimit.hom_ext
  intro j
  change colimit.ι (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) j ≫
    colim.map (Functor.whiskerLeft (latchingSource simplexOp (Opposite.op ⦋n⦌))
      (simplicialReplacementRowsMap η)) ≫ colimit.desc _ (simplicialReplacementRowLatchingCocone G n) =
    colimit.ι (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) j ≫
      colimit.desc _ (simplicialReplacementRowLatchingCocone F n) ≫
        simplicialReplacementRowPartMap η n ((nerve I).degenerate n)
  simp only [colimit.ι_map_assoc, colimit.ι_desc_assoc, colimit.ι_desc, Functor.whiskerLeft_app]
  exact simplicialReplacementRowLatchingLeg_map n η j

/-- 逆向きの同じ同型は、元のlatching評価の係数射を回収する。 -/
theorem simplicialReplacementRowLatchingIso_inv_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫
      (simplicialReplacementRowLatchingIso G n).inv =
    (simplicialReplacementRowLatchingIso F n).inv ≫
      (latchingEvaluation simplexOp (Opposite.op ⦋n⦌)).map (simplicialReplacementRowsMap η) := by
  apply (cancel_mono (simplicialReplacementRowLatchingIso G n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    simplicialReplacementRowLatchingIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 逆向きの同じ同型で元の境界比較を戻すと、同じ退化部分の包含になる。 -/
theorem simplicialReplacementRowLatchingIso_inv_inclusion (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).inv ≫
      (latchingComparison simplexOp (Opposite.op ⦋n⦌)).app (simplicialReplacementRows F) =
      (simplicialReplacementDegenerateRow F n).ι := by
  rw [← simplicialReplacementRowLatchingIso_inclusion, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
