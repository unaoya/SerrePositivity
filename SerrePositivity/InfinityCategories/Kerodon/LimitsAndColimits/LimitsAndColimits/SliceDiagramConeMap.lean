module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceDiagramIso

/-!
概要：反転と図式同型による余錐の脚の比較を整備する。
方針：join の混合辺と固定図式の輸送の射を計算する。
規約：添字や標的の quasicategory 性を追加で要求しない。
使われ方：B5 の指定単位を伴う左 Kan の局所余錐の比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- 概要：図式の等式で錐を輸送しても元の射は変わらない。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
lemma sliceOver_cast_val {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver h)).hom.app (Opposite.op ⦋0⦌) c).val = c.val := by
  cases h
  rfl

/-- 概要：図式同型による錐の像の元の射を前後合成で表示する。
方針：反転の切断と図式同型の前後合成を計算する。
規約：元の指定図式・頂点・脚を保持する。
使われ方：B5 の左局所余錐の古典比較。 -/
lemma sliceDiagramIso_hom_val {K L X Y : SSet.{u}} (e : K ≅ L) (f : X ≅ Y)
    (p : K ⟶ X) (q : L ⟶ Y) (h : p ≫ f.hom = e.hom ≫ q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceDiagramIso e f p q h).hom.app (Opposite.op ⦋0⦌) c).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) e.inv ≫ c.val ≫ f.hom := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceDiagramIso, Iso.trans_hom, asIso_hom]
  simp only [NatTrans.comp_app_apply]
  rw [sliceOver_cast_val]
  rfl
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
