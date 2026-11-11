module
public import SerrePositivity.KST.SConstruction.CoherentPathInsertionDiamond

/-! # 二点挿入の四辺と元の端点 Path の合成辺
概要：二つの挿入経路の四辺を、元の合成比較辺と左右の固定 Path との合成へ照合する。
方針：全一単体の始点・終点の Path の集合を比較し、元の包含射の一意性を使う。
規約：辺の成分や類ではなく、全一単体の等号を証明する。
使われ方：三入力の実二単体の四辺を元の豊穣比較とその合成へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {J : Type u} [LinearOrder J] {a b c d : J}

/-- 端点 Path への挿入辺は、元の同じ長辺から合成への包含辺そのもの。 -/
lemma coherentInsertEndpoint_edge (hab : a ≤ b) (hbc : b ≤ c) :
    (nerve.edgeMk ((coherentPathInsertTransformation hab hbc).app
      (coherentEndpointPath (hab.trans hbc)))).edge =
      (nerve.edgeMk (coherentEndpointPathToComposite hab hbc)).edge := by
  refine ComposableArrows.ext₁ rfl (coherentPathInsert_endpoint hab hbc) ?_
  apply InducedCategory.hom_ext
  exact Subsingleton.elim _ _

/-- 第一挿入後の辺は、固定前半と後半の元の比較辺を合成した全一単体。 -/
lemma coherentDoubleInsertFirstUpper_edge (hab : a ≤ b) (hbd : b ≤ d) (hdc : d ≤ c) :
    (nerve.edgeMk ((coherentPathInsertTransformation (hab.trans hbd) hdc).app
      (coherentPathInsert hab (hbd.trans hdc)
        (coherentEndpointPath ((hab.trans hbd).trans hdc))))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a b c).app (Opposite.op ⦋1⦌)
        ((nerve.edgeMk (𝟙 (coherentEndpointPath hab))).edge,
          (nerve.edgeMk (coherentEndpointPathToComposite hbd hdc)).edge) := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · apply SimplicialThickening.Path.ext
    ext x
    change ((x = a ∨ x = c) ∨ x = b) ↔ ((x = a ∨ x = b) ∨ (x = b ∨ x = c))
    tauto
  · apply SimplicialThickening.Path.ext
    ext x
    change (((x = a ∨ x = c) ∨ x = b) ∨ x = d) ↔
      ((x = a ∨ x = b) ∨ ((x = b ∨ x = d) ∨ (x = d ∨ x = c)))
    tauto
  · apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

/-- 第二挿入後の辺は、前半の元の比較辺と固定後半を合成した全一単体。 -/
lemma coherentDoubleInsertSecondUpper_edge (hab : a ≤ b) (hbd : b ≤ d) (hdc : d ≤ c) :
    (nerve.edgeMk (coherentDoubleInsertSecondInclusion hab (hbd.trans hdc)
      (hab.trans hbd) hdc (coherentEndpointPath ((hab.trans hbd).trans hdc)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a d c).app (Opposite.op ⦋1⦌)
        ((nerve.edgeMk (coherentEndpointPathToComposite hab hbd)).edge,
          (nerve.edgeMk (𝟙 (coherentEndpointPath hdc))).edge) := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · apply SimplicialThickening.Path.ext
    ext x
    change ((x = a ∨ x = c) ∨ x = d) ↔ ((x = a ∨ x = d) ∨ (x = d ∨ x = c))
    tauto
  · apply SimplicialThickening.Path.ext
    ext x
    change (((x = a ∨ x = c) ∨ x = b) ∨ x = d) ↔
      (((x = a ∨ x = b) ∨ (x = b ∨ x = d)) ∨ (x = d ∨ x = c))
    tauto
  · apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

end SerrePositivity.KST.SConstruction
