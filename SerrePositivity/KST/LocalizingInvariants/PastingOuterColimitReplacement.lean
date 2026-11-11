module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingExtension

/-!
概要：左押し出しを含む長方形の外周を、同じ span 上の指定押し出しへ取り替える。
方針：四頂点への余錐の厳密延長を経て、五頂点の普遍余錐を付加する。
規約：五頂点の図式と外周正方形を等号で保持。使われ方：graph pullback の双対貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma pastingOuterCocone_standard_val {X : SSet.{u}}
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterCocone F).restrict
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι)).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1 := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ (𝟙 Δ[0]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone ≫ F)) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare, Category.assoc] using
    congrArg (fun t => t ≫ F) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerCocone_outerSpan

lemma exists_pasting_outer_colimit_replacement {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2))
    (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare S)
    (hbase : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan S) :
    ∃ F' : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ F' = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ F ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F' 0) ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F' 1 = S := by
  let p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι ≫ F
  let k := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι
  have hk : k ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan S := by
    change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι ≫ F) = _
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1 := by
        simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare, Category.assoc] using
          congrArg (fun t => t ≫ F) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso_hom_ι
      _ = _ := hbase
  let d₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (k ≫ p) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone S).val, by rw [hk]; exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone S).property⟩
  have hd₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d₀ :=
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq d₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone S) rfl).2 hS
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  obtain ⟨d, hd, hdk, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCocone_extension_of_trivialRestriction p k d₀ hd₀
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerLeftDiagram (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ F)) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)
    exact hl
  obtain ⟨F', hcorner, hr, hout⟩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pastingExtension_of_outerColimit (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ F) hleft d hd
  refine ⟨F', hcorner, hr, ?_⟩
  apply (cancel_epi _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom).1
  rw [← pastingOuterCocone_standard_val]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap k (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterCocone F').val = _
  rw [hout]
  exact congrArg Subtype.val hdk

end SerrePositivity.KST.LocalizingInvariants
