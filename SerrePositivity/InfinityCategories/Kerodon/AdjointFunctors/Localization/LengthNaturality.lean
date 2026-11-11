module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthColimit

/-!
# 長さ濾過の元の図式の比較に対する自然性

概要：元の自然変換は全長さ段階と Nat 図式に作用し、同じ元の余極限の射を回収する。
方針：全てを固定語の標準射で照合する。
規約：任意の同型で比較を代用せず、元の colim.map そのものへの一致を証明する。
使われ方：段階ごとの弱同値から元の全語の余極限の弱同値への移送。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)

def lengthStageMap (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage F n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage G n :=
  colim.map (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion n) η)

lemma lengthStageInclusion_map (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : a.length ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a ha ≫ lengthStageMap η n =
      η.app a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion G n a ha :=
  colimit.ι_map (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion n) η) ⟨a, ha⟩

lemma lengthStageMap_transition {n m : ℕ} (h : n ≤ m) :
    lengthStageMap η n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition G h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F h ≫ lengthStageMap η m := by
  apply colimit.hom_ext (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion n ⋙ F)
  intro a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj a.property ≫
    (lengthStageMap η n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition G h) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj a.property ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F h ≫ lengthStageMap η m)
  calc
    _ = η.app a.obj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion G m a.obj (a.property.trans h) := by
      rw [← Category.assoc, lengthStageInclusion_map, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_transition]
    _ = _ := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_transition, lengthStageInclusion_map]

def lengthDiagramMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram G where
  app n := lengthStageMap η n
  naturality _ _ f := (lengthStageMap_transition η (leOfHom f)).symm

lemma lengthStageToColimit_map (n : ℕ) :
    lengthStageMap η n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit G n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit F n ≫ colim.map η := by
  apply colimit.hom_ext (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion n ⋙ F)
  intro a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj a.property ≫
    (lengthStageMap η n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit G n) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj a.property ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit F n ≫ colim.map η)
  calc
    _ = η.app a.obj ≫ colimit.ι G a.obj := by
      rw [← Category.assoc, lengthStageInclusion_map, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_toColimit]
    _ = _ := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_toColimit, colimit.ι_map]

lemma lengthColimitIso_naturality :
    colim.map (lengthDiagramMap η) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso G).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso F).hom ≫ colim.map η := by
  apply colimit.hom_ext (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram F)
  intro n
  calc
    _ = lengthStageMap η n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit G n := by
      rw [← Category.assoc, colimit.ι_map, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso_fac]
      rfl
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit F n ≫ colim.map η := lengthStageToColimit_map η n
    _ = _ := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso_fac]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
