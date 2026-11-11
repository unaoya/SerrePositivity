module

public import SerrePositivity.EInfinity.SimplicialLocalization.EnrichedMap

/-!
# 単体的局所化の係数射の恒等・合成則

概要：Dwyer–Kan の固定 Hom と豊穣係数射の厳密な関手則を証明する。
方針：全解像の係数関手の恒等・合成を各 Hom に移して対象移送を相殺する。
規約：元の係数射と同じ対象表示を保持する。
使われ方：Kan 化と coherent nerve での係数関手性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory

/-- 概要：恒等相対関手は固定 Hom の恒等単体写像を誘導する（Dwyer–Kan）。
方針：局所化解像の恒等則を Hom に評価して対象移送を相殺する。
規約：全次数の実際の Hom を使う。
使われ方：豊穣係数射の恒等則。 -/
lemma localizationHomMap_id (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    localizationHomMap (𝟙 C) X Y = 𝟙 (localizationHom C X Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  have h := congrArg Cat.Hom.toFunctor
    (NatTrans.congr_app (localizedFreeResolutionFunctor.map_id C) n)
  change ((localizedFreeResolutionMap (𝟙 C)).app n).toFunctor = 𝟭 _ at h
  change (localizationHomMap (𝟙 C) X Y).app n f = f
  dsimp only [localizationHomMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans,
    TypeCat.ofHom_apply]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap
  rw [Functor.congr_hom h f]
  simp

/-- 概要：相対関手の合成は固定 Hom の係数写像の合成を誘導する（Dwyer–Kan）。
方針：全解像の合成則を Hom に評価し、中間対象の移送を相殺する。
規約：元の相対関手の合成順序を保持する。
使われ方：豊穣係数射の合成則。 -/
lemma localizationHomMap_comp {C D E : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) (G : D ⟶ E)
    (X Y : C.category) :
    localizationHomMap (F ≫ G) X Y =
      localizationHomMap F X Y ≫ localizationHomMap G (F.functor.obj X) (F.functor.obj Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  have h := congrArg Cat.Hom.toFunctor
    (NatTrans.congr_app (localizedFreeResolutionFunctor.map_comp F G) n)
  change ((localizedFreeResolutionMap (F ≫ G)).app n).toFunctor =
    ((localizedFreeResolutionMap F).app n).toFunctor ⋙
      ((localizedFreeResolutionMap G).app n).toFunctor at h
  change (localizationHomMap (F ≫ G) X Y).app n f =
    (localizationHomMap G (F.functor.obj X) (F.functor.obj Y)).app n
      ((localizationHomMap F X Y).app n f)
  dsimp only [localizationHomMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans,
    TypeCat.ofHom_apply]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap
  rw [Functor.congr_hom h f]
  simp only [Functor.comp_map, Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]

/-- 概要：恒等相対関手は恒等豊穣関手を誘導する（Dwyer–Kan）。
方針：同じ対象写像と各 Hom の恒等則を束ねる。
規約：豊穣関手の厳密な等式。
使われ方：Kan 化の係数関手の恒等則。 -/
lemma localizationEnrichedMap_id (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    localizationEnrichedMap (𝟙 C) = EnrichedFunctor.id SSet (LocalizationObjects C) := by
  refine EnrichedFunctor.ext SSet (F := localizationEnrichedMap (𝟙 C))
    (G := EnrichedFunctor.id SSet (LocalizationObjects C)) (fun _ => rfl) ?_
  intro X Y
  change localizationHomMap (𝟙 C) X Y ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id]
  exact localizationHomMap_id C X Y

/-- 概要：相対関手の合成は豊穣係数射の合成を誘導する（Dwyer–Kan）。
方針：同じ対象写像と各 Hom の合成則を束ねる。
規約：同じ豊穣構造と合成を保持する。
使われ方：coherent nerve の係数関手の合成則。 -/
lemma localizationEnrichedMap_comp {C D E : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) (G : D ⟶ E) :
    localizationEnrichedMap (F ≫ G) =
      (localizationEnrichedMap F).comp SSet (localizationEnrichedMap G) := by
  refine EnrichedFunctor.ext SSet (F := localizationEnrichedMap (F ≫ G))
    (G := (localizationEnrichedMap F).comp SSet (localizationEnrichedMap G))
    (fun _ => rfl) ?_
  intro X Y
  change localizationHomMap (F ≫ G) X Y ≫ 𝟙 _ =
    localizationHomMap F X Y ≫ localizationHomMap G (F.functor.obj X) (F.functor.obj Y)
  rw [Category.comp_id]
  exact localizationHomMap_comp F G X Y

end SerrePositivity.EInfinity.SimplicialLocalization
