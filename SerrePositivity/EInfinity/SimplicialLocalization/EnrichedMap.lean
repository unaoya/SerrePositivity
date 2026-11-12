module

public import SerrePositivity.EInfinity.SimplicialLocalization.Enrichment
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality
public import SerrePositivity.EInfinity.SimplicialLocalization.LocalizedResolutionFunctoriality

/-!
# 相対関手の単体的局所化への延長

概要：Dwyer–Kan の単体的局所化に元の相対関手を豊穣関手として送る。
方針：全局所化解像の係数射と対象表示の保存を固定 Hom へ代入する。
規約：全次数の元の射・単位・合成を保持する。
使われ方：Kan 化と coherent nerve の後の ∞ 関手。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory

/-- 概要：相対関手は局所化 Hom の間の単体写像を与える（Dwyer–Kan）。
方針：同じ全解像の係数自然変換を固定 Hom の一般界面へ送る。
規約：各次数の係数関手の元の Hom 作用を保持する。
使われ方：局所化の豊穣関手の Hom 成分。 -/
def localizationHomMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) (X Y : C.category) :
    localizationHom C X Y ⟶ localizationHom D (F.functor.obj X) (F.functor.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (localizedFreeResolution C) (localizedFreeResolution D)
    (localizedFreeResolutionObject C) (localizedFreeResolutionObject D)
    (fun θ X => localizedFreeResolutionObject_naturality C θ X)
    (fun θ X => localizedFreeResolutionObject_naturality D θ X)
    (localizedFreeResolutionMap F) F.functor.obj
    (fun n X => localizedFreeResolutionMap_object F n X) X Y

/-- 概要：相対関手は単体的局所化の豊穣関手を与える（Dwyer–Kan）。
方針：固定 Hom の係数射の単位・合成保存を各次数で照合する。
規約：元の相対関手の対象写像と実際の局所化 Hom を保持する。
使われ方：忘却関手や離散対象関手の ∞ 関手化。 -/
def localizationEnrichedMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    EnrichedFunctor SSet.{u} (LocalizationObjects C) (LocalizationObjects D) where
  obj := F.functor.obj
  map := localizationHomMap F
  map_id X := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap_identity
      (localizedFreeResolution C) (localizedFreeResolution D)
      (localizedFreeResolutionObject C) (localizedFreeResolutionObject D)
      (localizedFreeResolutionMap F) F.functor.obj
      (fun n X => localizedFreeResolutionMap_object F n X) n X
  map_comp X Y Z := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro q
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap_composition
      (localizedFreeResolution C) (localizedFreeResolution D)
      (localizedFreeResolutionObject C) (localizedFreeResolutionObject D)
      (localizedFreeResolutionMap F) F.functor.obj
      (fun n X => localizedFreeResolutionMap_object F n X) n q.1 q.2

/-- 概要：同じ豊穣係数射は基礎の単体的圏の関手を与える（Dwyer–Kan）。
方針：元の豊穣関手の ForgetEnrichment を使う。
規約：同じ対象写像と Hom 作用。
使われ方：Kan 化前の係数関手。 -/
def localizationFunctor {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    LocalizationCategory C ⥤ LocalizationCategory D :=
  (localizationEnrichedMap F).forget

end SerrePositivity.EInfinity.SimplicialLocalization
