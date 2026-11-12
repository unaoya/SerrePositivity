module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-! # 実比較同値による関手同型の反映
概要：同値との前後合成で得た関手同型を、元の二つの射の関手同型へ戻す。
方針：元の逆射と指定された逆律を前後合成する。
規約：同型の存在を追加仮定しない。使われ方：標準 DK と native dg 評価比較の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 同じ比較同値との前合成は、元の射の関手同型を反映する。 -/
def functorIsoReflectPreEquivalence {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y)
    {f g : Y ⟶ Z} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ f) (e.hom ≫ g)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f (e.inv ≫ (e.hom ≫ f)) := by
    simpa only [Category.assoc, Category.id_comp] using (e.invHomIso.postcomp f).symm
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.inv ≫ (e.hom ≫ g)) g := by
    simpa only [Category.assoc, Category.id_comp] using e.invHomIso.postcomp g
  exact hf ≪≫ h.precomp e.inv ≪≫ hg

/-- 同じ比較同値との後合成は、元の射の関手同型を反映する。 -/
def functorIsoReflectPostEquivalence {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y Z)
    {f g : X ⟶ Y} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ e.hom) (g ≫ e.hom)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f ((f ≫ e.hom) ≫ e.inv) := by
    simpa only [Category.assoc, Category.comp_id] using (e.homInvIso.precomp f).symm
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((g ≫ e.hom) ≫ e.inv) g := by
    simpa only [Category.assoc, Category.comp_id] using e.homInvIso.precomp g
  exact hf ≪≫ h.postcomp e.inv ≪≫ hg

end SerrePositivity.KST.SConstruction
