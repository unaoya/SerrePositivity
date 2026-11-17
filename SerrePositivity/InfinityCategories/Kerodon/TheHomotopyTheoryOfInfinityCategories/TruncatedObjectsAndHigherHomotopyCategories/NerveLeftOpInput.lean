module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOppositeInverseNaturality

/-!
概要：反変の通常関手の nerve 入力を同じ leftOp と二重反転で表す。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 同じ反変関手の nerve 入力は、同じ leftOp と既存の二重反転による入力と一致する。 -/
lemma sameNerveLeftOp_input {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ Dᵒᵖ) :
    nerveMap F ≫ (nerveOppositeIso (C := D)).inv =
      (nerveMap (opOp C) ≫ (nerveOppositeIso (C := Cᵒᵖ)).inv) ≫
        SSet.opFunctor.map (nerveMap F.leftOp) := by
  have h : opOp C ⋙ F.leftOp.op = F := rfl
  have hn : nerveMap (opOp C) ≫ nerveMap F.leftOp.op = nerveMap F := by
    change nerveMap (opOp C ⋙ F.leftOp.op) = nerveMap F
    rw [h]
  rw [← hn, Category.assoc, nerveOppositeIso_inv_naturality]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
