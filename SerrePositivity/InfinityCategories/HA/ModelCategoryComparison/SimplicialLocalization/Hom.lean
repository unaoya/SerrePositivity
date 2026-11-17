module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ResolutionObjects
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 固定対象の Dwyer–Kan Hom の単体集合

概要：Dwyer–Kan の次数ごとの局所化の射を固定した両対象の単体集合へ束ねる。
方針：元の対象表示と全作用素との自然性を固定 Hom の一般構成へ代入する。
規約：合成と単位は各次数の局所化圏の同じもの。
使われ方：厳密な単体的豊穣圏の構成と Hom の Kan 化。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 概要：元の両対象の局所化した自由解像の Hom の単体集合（Dwyer–Kan）。
方針：同じ対象表示と全作用素による保存を固定 Hom 関手へ代入する。
規約：全次数の局所化圏の実際の Hom を使う。
使われ方：単体的局所化の豊穣 Hom。 -/
def localizationHom (X Y : C.category) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_naturality C θ X) X Y

/-- 概要：同じ次数の恒等射は Hom の自然な単体的単位（Dwyer–Kan）。
方針：全作用素による恒等射の保存を使う。
規約：全次数の元の恒等射を保持する。
使われ方：豊穣圏の単位。 -/
def localizationIdentity (X : C.category) : 𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X X where
  app n := ↾fun _ => 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C n X)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map_identity (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C)
      (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_naturality C θ X) θ X).symm

/-- 概要：同じ次数の射の合成は Hom の単体的合成射（Dwyer–Kan）。
方針：全作用素による射の合成の保存を使う。
規約：合成射は各次数の元の合成そのもの。
使われ方：単体的局所化の豊穣合成。 -/
def localizationComposition (X Y Z : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y ⊗ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Z where
  app n := ↾fun q => q.1 ≫ q.2
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro q
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map _ _ _ θ q.1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map _ _ _ θ q.2 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map _ _ _ θ (q.1 ≫ q.2)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map_composition (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C)
      (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_naturality C θ X) θ q.1 q.2).symm

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
