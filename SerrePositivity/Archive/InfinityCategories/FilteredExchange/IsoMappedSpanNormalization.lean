module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.IsoEndpointNormalization

/-!
概要：関手で写した左右の指定比較と、外側の実頂点の補正を一つの合成式へ揃える。
方針：関手による補正の保存・二段の補正の合成・中間補正の相殺を順に適用する。
規約：全端点の等式を明示。使われ方：native path の指定像と元の fiber 可換同型の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v u' v'
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 共通対象での合成と外側の補正を写すと、補正後の二指定像の合成に等しい。 -/
lemma functor_mapIso_normalized_span {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {a b l r l₀ r₀ : C} (e : a ≅ l) (f : b ≅ r)
    (h : a = b) (hl : l = l₀) (hr : r = r₀)
    {a' b' l' r' : D} (ha : F.obj a = a') (hb : F.obj b = b')
    (hl' : F.obj l₀ = l') (hr' : F.obj r₀ = r') (h' : a' = b') :
    isoNormalizeEndpoints (F.mapIso (isoNormalizeEndpoints (e.symm ≪≫ eqToIso h ≪≫ f) hl hr))
      hl' hr' =
    (isoNormalizeEndpoints (F.mapIso e) ha ((congrArg F.obj hl).trans hl')).symm ≪≫
      eqToIso h' ≪≫ isoNormalizeEndpoints (F.mapIso f) hb ((congrArg F.obj hr).trans hr') := by
  rw [isoNormalizeEndpoints_map, isoNormalizeEndpoints_trans, functor_mapIso_span]
  exact (isoNormalizeEndpoints_span (F.mapIso e) (F.mapIso f) (congrArg F.obj h)
    ha hb ((congrArg F.obj hl).trans hl') ((congrArg F.obj hr).trans hr') h').symm

end SerrePositivity.InfinityCategories.F2
