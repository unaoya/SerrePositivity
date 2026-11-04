module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.KanModels.KanAnodyneLocalization
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanAnodyne
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence

/-! # 分数図式の亜群化に使う厳密な Kan 値の関手的模型 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 合成・恒等を厳密に保つ連続 Kan 置換を、小さい Kan 複体値の関手に束ねる。 -/
def strictKanCompletion : SSet.{u} ⥤ KanObject.{u} where
  obj X := ⟨F2.continuousKanReplacement.obj X, inferInstance⟩
  map f := F2.continuousKanReplacement.map f
  map_id X := F2.continuousKanReplacement.map_id X
  map_comp f g := F2.continuousKanReplacement.map_comp f g

/-- 元の anodyne 局所化同型は、同じ厳密 Kan 置換の実写像を同値にする。 -/
theorem strictKanCompletion_map_isQCatEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsQCatEquivalence (strictKanCompletion.map f) := by
  change IsQCatEquivalence (F2.continuousKanReplacement.map f)
  let Q := AnodyneHomotopy.anodyneQ
  have : IsIso (Q.map (F2.continuousKanReplacementUnit.app X)) :=
    SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne X)
  have : IsIso (Q.map (F2.continuousKanReplacementUnit.app Y)) :=
    SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne Y)
  have hn := congrArg Q.map (F2.continuousKanReplacementUnit.naturality f)
  change Q.map (f ≫ F2.continuousKanReplacementUnit.app Y) =
    Q.map (F2.continuousKanReplacementUnit.app X ≫ F2.continuousKanReplacement.map f) at hn
  rw [Q.map_comp, Q.map_comp] at hn
  have hc : IsIso (Q.map (F2.continuousKanReplacementUnit.app X) ≫
      Q.map (F2.continuousKanReplacement.map f)) := hn ▸ inferInstance
  exact isQCatEquivalence_of_anodyneQ_isIso _ ((isIso_comp_left_iff _ _).mp hc)

end SerrePositivity.KST.Fibration
