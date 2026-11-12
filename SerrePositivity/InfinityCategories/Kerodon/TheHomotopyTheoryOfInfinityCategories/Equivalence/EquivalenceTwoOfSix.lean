module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：同値と Kan 複体のホモトピー同値の二対六則。
方針：隣接する二つの合成の逆から中間の射の左右逆を比較する。
規約：モデル構造は使わない。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.8.3（Tag 05AW） の写像空間による同値の検出。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：隣接する二つの合成が同値なら中央の射は同値。
方針：一方の逆から左逆、他方の逆から右逆を作り、可逆二胞体で同定する。
規約：四つの単体集合は quasicategory。
使われ方：Kerodon §4.5.1（Tag 01DQ） の同値の二対六則。 -/
lemma isQCatEquivalence_of_composites {A B C D : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory D]
    {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    (hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (f ≫ g)) (hgh : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (g ≫ h)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g := by
  let L := h ≫ hgh.choose.inv
  let R := hfg.choose.inv ≫ f
  have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ L) (𝟙 B) := by
    have e := hgh.choose.homInvIso
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((g ≫ h) ≫ hgh.choose.inv) (𝟙 B) at e
    simpa only [L, Category.assoc] using e
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (R ≫ g) (𝟙 C) := by
    have e := hfg.choose.invHomIso
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (hfg.choose.inv ≫ (f ≫ g)) (𝟙 C) at e
    simpa only [R, Category.assoc] using e
  have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (R ≫ g ≫ L) L := by
    simpa only [Category.assoc, Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp hR L
  have e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (R ≫ g ≫ L) R := by
    simpa only [Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp hL R
  exact ⟨L, ⟨hL⟩, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (e₁.symm ≪≫ e₂) g ≪≫ hR⟩⟩

/-- 概要：Kan 複体間で隣接する二つの合成がホモトピー同値なら中央の射も同値。
方針：quasicategory の同値の二対六則から実際のホモトピー逆へ戻す。
規約：四つの単体集合の Kan 性を仮定する。
使われ方：Kerodon §4.8.3（Tag 05AW） の写像空間の二対六則。 -/
lemma isSimplicialHomotopyEquivalence_of_composites {A B C D : SSet.{u}}
    [KanComplex A] [KanComplex B] [KanComplex C] [KanComplex D]
    {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    (hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ≫ g))
    (hgh : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (g ≫ h)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g :=
  (isQCatEquivalence_of_composites hfg.isQCatEquivalence
    hgh.isQCatEquivalence).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
