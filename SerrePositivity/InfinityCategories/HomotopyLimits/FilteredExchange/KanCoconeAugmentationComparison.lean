module

public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.CoconeHomWeightedComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanCoconeColimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedBousfieldKanColimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedRepresentableComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.RepresentableComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedColimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedSections

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
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I] {F : I ⥤ KanObject.{u}}

/-- 概要：Kan 余錐の標準表現可能比較は反転 augmentation の前合成に一致する。
方針：一般の Hom 錐の公式を反対 Kan 圏の Hom 関手の等式で移す。
規約：coend の Hom の標準同型を使う。使われ方：普遍性判定への入力。 -/
lemma kanCoconeAugmentationComparison_factor (c : Cocone F) (Y : KanObject.{u}) :
    SSet.opFunctor.map ((pre (weightedColimitAugmentation
      (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) (kanObjectForget.mapCocone c))).app Y.obj) ≫
        (kanReflectedBousfieldKanColimitUnderlyingHomIso F Y).hom =
      reflectedRepresentableComparison c.op (Opposite.op Y) := by
  have h := coconeHomCone_reflectedWeightedComparison (bousfieldKanWeight Iᵒᵖ)
    (kanObjectForget.mapCocone c) Y.obj
  let G₀ : KanObject.{u}ᵒᵖ ⥤ SSet.{u} :=
    kanObjectForget.op ⋙ (internalHom (C := SSet.{u})).flip.obj Y.obj
  have e₀ : weightedColimitHomDiagram (F ⋙ kanObjectForget) Y.obj = F.op ⋙ G₀ := rfl
  have hcone : G₀.mapCone c.op = coconeHomCone (kanObjectForget.mapCocone c) Y.obj := rfl
  have ht (G : KanObject.{u}ᵒᵖ ⥤ SSet.{u}) (hG : G = G₀) :
      SSet.opFunctor.map ((pre (weightedColimitAugmentation
        (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) (kanObjectForget.mapCocone c))).app Y.obj) ≫
          (reflectedWeightedColimitHomIso (bousfieldKanWeight Iᵒᵖ)
            (F ⋙ kanObjectForget) Y.obj).hom ≫
          eqToHom (congrArg (fun D ↦ bousfieldKanHolim (D ⋙ SSet.opFunctor))
            (e₀.trans (congrArg (fun D ↦ F.op ⋙ D) hG.symm))) =
        eqToHom (congrArg (fun D ↦ (D.obj (Opposite.op c.pt)).op) hG.symm) ≫
          weightedConeComparison (bousfieldKanWeight Iᵒᵖ)
            (SSet.opFunctor.mapCone (G.mapCone c.op)) := by
    subst G
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    simpa only [hcone] using! h
  simpa only [kanReflectedBousfieldKanColimitUnderlyingHomIso, Iso.trans_hom, Category.assoc,
    reflectedRepresentableComparison, reflectedSimplicialHomCone, simplicialHomCone,
    simplicialHomDiagram, eqToHom_refl, Category.id_comp] using!
      ht _ (kanObjectOppositeHomFunctor_eq Y)

end SerrePositivity.InfinityCategories.F2
