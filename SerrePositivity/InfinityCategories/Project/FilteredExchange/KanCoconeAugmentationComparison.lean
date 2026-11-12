module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeHomWeightedComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanCoconeColimits
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedBousfieldKanColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedRepresentableComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.RepresentableComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSections

/-!
概要：Kan 値の通常の余錐の反転した表現可能比較を augmentation で表示する。
方針：反変内部 Hom の錐を反対圏の豊穣 Hom 錐と同定する。
規約：余錐の頂点と全ての脚を保持する。
使われ方：通常の filtered colimit 余錐自体の native な普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I] {F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}

/-- 概要：Kan 余錐の標準表現可能比較は反転 augmentation の前合成に一致する。
方針：一般の Hom 錐の公式を反対 Kan 圏の Hom 関手の等式で移す。
規約：coend の Hom の標準同型を使う。使われ方：普遍性判定への入力。 -/
lemma kanCoconeAugmentationComparison_factor (c : Cocone F) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    SSet.opFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c))).app Y.obj) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitUnderlyingHomIso F Y).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c.op (Opposite.op Y) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeHomCone_reflectedWeightedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c) Y.obj
  let G₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ ⥤ SSet.{u} :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.op ⋙ (internalHom (C := SSet.{u})).flip.obj Y.obj
  have e₀ : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) Y.obj = F.op ⋙ G₀ := rfl
  have hcone : G₀.mapCone c.op = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeHomCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c) Y.obj := rfl
  have ht (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ ⥤ SSet.{u}) (hG : G = G₀) :
      SSet.opFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c))).app Y.obj) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ)
            (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) Y.obj).hom ≫
          eqToHom (congrArg (fun D ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (D ⋙ SSet.opFunctor))
            (e₀.trans (congrArg (fun D ↦ F.op ⋙ D) hG.symm))) =
        eqToHom (congrArg (fun D ↦ (D.obj (Opposite.op c.pt)).op) hG.symm) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ)
            (SSet.opFunctor.mapCone (G.mapCone c.op)) := by
    subst G
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    simpa only [hcone] using! h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitUnderlyingHomIso, Iso.trans_hom, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplicialHomCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram, eqToHom_refl, Category.id_comp] using!
      ht _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectOppositeHomFunctor_eq Y)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
