module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthDiagram

/-!
# 元の全語の余極限の長さ濾過による回収

概要：元の長さ制限の各段階を Nat に沿って余極限に取ると、元の全語の余極限になる。
方針：任意の段階の余錐を全語の余錐へ戻し、両方の普遍性を元の標準射で証明する。
規約：段階の単射性・proper 性は不要で、元の全語の圏を filtered とは扱わない。
使われ方：Dwyer–Kan §4.2、Nat の filtered 余極限による弱同値の移送。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w})

lemma lengthCocone_component (c : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram F)) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    {n : ℕ} (ha : a.length ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F a.length a (le_refl _) ≫ c.ι.app a.length =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a ha ≫ c.ι.app n := by
  have hc := c.ι.naturality (homOfLE ha)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F ha ≫ c.ι.app n = c.ι.app a.length ≫ 𝟙 _ at hc
  rw [Category.comp_id] at hc
  rw [← hc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_transition]

/-- 元の全段階の余錐から、同じ元の全語の余錐を回収する。 -/
def lengthReconstructedCocone (c : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram F)) : Cocone F where
  pt := c.pt
  ι :=
    { app a := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F a.length a (le_refl _) ≫ c.ι.app a.length
      naturality a b f := by
        change F.map f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F b.length b (le_refl _) ≫ c.ι.app b.length) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F a.length a (le_refl _) ≫ c.ι.app a.length) ≫ 𝟙 _
        rw [Category.comp_id, lengthCocone_component F c a (Nat.le_max_left _ b.length),
          lengthCocone_component F c b (Nat.le_max_right a.length _), ← Category.assoc,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_naturality] }

/-- 元の全語の余極限は、元の長さ制限段階の余極限でもある。 -/
def lengthCocone_isColimit : IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthCocone F) where
  desc c := colimit.desc F (lengthReconstructedCocone F c)
  fac c n := by
    apply colimit.hom_ext
    intro a
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj a.property ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit F n ≫ colimit.desc F (lengthReconstructedCocone F c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a.obj a.property ≫ c.ι.app n
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_toColimit, colimit.ι_desc]
    exact lengthCocone_component F c a.obj a.property
  uniq c f hf := by
    apply colimit.hom_ext (F := F)
    intro a
    rw [colimit.ι_desc]
    have he := hf a.length
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit F a.length ≫ f = c.ι.app a.length at he
    change colimit.ι F a ≫ f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F a.length a (le_refl _) ≫ c.ι.app a.length
    rw [← he, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_toColimit]

/-- 元の標準射で定まる、反復余極限と全語の余極限の同型。 -/
def lengthColimitIso : colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram F) ≅ colimit F :=
  (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram F)).coconePointUniqueUpToIso (lengthCocone_isColimit F)

lemma lengthColimitIso_fac (n : ℕ) :
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram F) n ≫ (lengthColimitIso F).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit F n :=
  (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram F)).comp_coconePointUniqueUpToIso_hom
    (lengthCocone_isColimit F) n

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
