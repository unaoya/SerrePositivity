module
public import SerrePositivity.KST.Spectra.PointedCofiberMappingNaturality

/-! # 元の二つの源の前合成と元の実合成
概要：点つき Hom の二前合成と元の実合成との一致を、基礎の全単体射で表示する。
方針：既存の点つき閉構造の自然性を同じ基礎写像へ戻す。
規約：成分やホモトピー類への移行を用いない。
使われ方：単射源に移した元の三円柱を保存済み補正列へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra

/-- 二つの元の源の制限は、元の実合成による一回の制限を回収する。 -/
lemma pointedMapping_pre_comp {A B C Z : PointedSimplicialSet.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre g Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f ≫ g) Z := by
  have h : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed g Z ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed f Z =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (f ≫ g) Z := by
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map]
  exact congrArg Under.Hom.right h

/-- suspension した二つの元の制限も、元の実合成の suspension による一制限。 -/
lemma pointedMapping_pre_suspension_comp {A B C Z : PointedSimplicialSet.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ g) Z ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ f) Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ (f ≫ g)) Z :=
  (pointedMapping_pre_comp _ _).trans
    (congrArg (fun h => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre h Z) (whiskerLeft_comp _ f g).symm)

end SerrePositivity.KST.SConstruction
