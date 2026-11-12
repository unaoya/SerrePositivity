module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction

/-!
概要：可換な同型の四角形から図式上の slice の同型を構成する。
方針：標的の後合成・添字の制限・図式の等式による輸送を合成する。
規約：quasicategory 性を仮定せず、標的への射影も保持する。
使われ方：B5 の局所余極限と pointwise Kan の古典比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：図式の始域と標的の同型から slice の同型を構成する。
方針：後合成・制限・等式による輸送の射影公式を使う。
規約：四角形の可換性を射の厳密な等式で指定する。
使われ方：B5 の局所余極限の双方向比較。 -/
def sliceDiagramIso {K L X Y : SSet.{u}} (e : K ≅ L) (f : X ≅ Y)
    (p : K ⟶ X) (q : L ⟶ Y) (h : p ≫ f.hom = e.hom ≫ q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_isIso p f.hom
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_isIso (p ≫ f.hom) e.inv
  have he : e.inv ≫ (p ≫ f.hom) = q := by
    rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p f.hom) ≪≫
    asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (p ≫ f.hom) e.inv) ≪≫ eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver he)

/-- 概要：図式比較の slice 同型は標的への射影を保つ。
方針：後合成・制限・等式による輸送の射影公式を使う。
規約：四角形の可換性を射の厳密な等式で指定する。
使われ方：B5 の局所余極限の双方向比較。 -/
lemma sliceDiagramIso_projection {K L X Y : SSet.{u}} (e : K ≅ L) (f : X ≅ Y)
    (p : K ⟶ X) (q : L ⟶ Y) (h : p ≫ f.hom = e.hom ≫ q) :
    (sliceDiagramIso e f p q h).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p ≫ f.hom := by
  dsimp only [sliceDiagramIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverProjection_eqTransport,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverRestrict_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection]
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 概要：単体集合の同型を頂点の全単射へ写す。
方針：後合成・制限・等式による輸送の射影公式を使う。
規約：四角形の可換性を射の厳密な等式で指定する。
使われ方：B5 の局所余極限の双方向比較。 -/
def isoVertexEquiv {X Y : SSet.{u}} (e : X ≅ Y) : X _⦋0⦌ ≃ Y _⦋0⦌ :=
  Equiv.ofBijective (fun x ↦ e.hom.app _ x) ((isIso_iff_bijective _).1 inferInstance)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
