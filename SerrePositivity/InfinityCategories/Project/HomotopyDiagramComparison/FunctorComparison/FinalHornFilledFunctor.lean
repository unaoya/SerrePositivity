module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornFillHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.UnitComposition

/-!
# 最終外側ホーンの豊穣単体への復元

概要：最終外側ホーンの二つの未知 Hom を、元の豊穣単体と相対充填へ組み立てる。
方針：全三対象の合成、全既知面への制限、薄い底の一意性を順に照合する。
規約：元の cf 置換と底射影を使い、内ホーンの欠損頂点条件を仮定しない。
使われ方：HTT 5.2.4.6 の元の右 Quillen 候補辺の Cartesian 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)
  (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up (Fin.last (n + 2)))) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))))
  (f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)))

/-- 前半の未知 Hom は、全境界上の合成面条件から全内部切断点で合成を保存する。 -/
lemma finalHornFillHom_comp_front
    (hf : ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom σ j)
    (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{u} (0 : Fin (n + 3))) (ULift.up b)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f 0 (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f 0 b ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) ≫
        SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_front,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_known σ g f 0 b (Fin.zero_le b) (Or.inr hbp),
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_known σ g f b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (le_of_lt hbp)
      (Or.inl (ne_of_gt hb0))]
  have hb := hf (.inr ⟨ULift.up.{u} b, hb0, hbp⟩)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontCompositionHom σ b hb0 hbp at hb
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι, Category.assoc, hb]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_on_product σ 0 b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)
    (Fin.zero_le b) (le_of_lt hbp) (Or.inr hbp) (Or.inl (ne_of_gt hb0))

/-- 全区間の未知 Hom は、既知合成面と penultimate 合成面の条件から合成を保存する。 -/
lemma finalHornFillHom_comp_full
    (hg : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ b hb0 hbp)
    (hfg : f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow σ) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g)
    (b : Fin (n + 3)) (hb0 : 0 < b) (hbn : b < Fin.last (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{u} (0 : Fin (n + 3))) (ULift.up b)
      (ULift.up (Fin.last (n + 2))) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f 0 (Fin.last (n + 2)) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f 0 b ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f b (Fin.last (n + 2))) ≫
        SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_full,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_known σ g f b (Fin.last (n + 2)) (Fin.le_last b)
      (Or.inl (ne_of_gt hb0))]
  by_cases hbp : b = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n
  · subst b
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_front, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontHom_postcomposition_composition σ g f hfg]
    simp only [Iso.hom_inv_id_assoc]
  · have hbp' := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.lt_finalHornPenultimate_of_lt_last_ne b hbn hbp
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_known σ g f 0 b (Fin.zero_le b) (Or.inr hbp'),
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι, Category.assoc, hg b hb0 hbp']
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornCompositionHom_on_product σ 0 b (Fin.last (n + 2))
      (Fin.zero_le b) (Fin.le_last b) (Or.inr hbp') (Or.inl (ne_of_gt hb0))

/-- 充填用 Hom は、順序外と単位を含む全三対象の元の豊穣合成を保存する。 -/
lemma finalHornFillHom_comp
    (hf : ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom σ j)
    (hg : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ b hb0 hbp)
    (hfg : f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow σ) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g) (a b c : Fin (n + 3)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{u} a) (ULift.up b) (ULift.up c) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f a c =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f a b ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f b c) ≫
        SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) := by
  by_cases hab : a ≤ b
  swap
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathProduct_empty_hom_ext (ULift.up.{u} a) (ULift.up b) (ULift.up c) (Or.inl hab) _ _
  by_cases hbc : b ≤ c
  swap
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathProduct_empty_hom_ext (ULift.up.{u} a) (ULift.up b) (ULift.up c) (Or.inr hbc) _ _
  by_cases heab : a = b
  · subst b
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHom_comp_left_unit _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_id σ g f a)
  by_cases hebc : b = c
  · subst c
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHom_comp_right_unit _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_id σ g f b)
  by_cases hpac : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a c
  · have hpab : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b := by
      rcases hpac with ha | hc
      · exact Or.inl ha
      · exact Or.inr (lt_of_le_of_lt hbc hc)
    have hpbc : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval b c := by
      rcases hpac with ha | hc
      · left
        intro hb
        exact ha (le_antisymm (hb ▸ hab) (Fin.zero_le a))
      · exact Or.inr hc
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_known σ g f a c (hab.trans hbc) hpac,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_known σ g f a b hab hpab,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_known σ g f b c hbc hpbc]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom_comp σ a b c hab hbc hpab hpbc hpac
  obtain ⟨rfl, hc | hc⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUnknownInterval_endpoints a c hpac
  · subst c
    exact finalHornFillHom_comp_front σ g f hf b
      (lt_of_le_of_ne hab heab) (lt_of_le_of_ne hbc hebc)
  · subst c
    exact finalHornFillHom_comp_full σ g f hg hfg b
      (lt_of_le_of_ne hab heab) (lt_of_le_of_ne hbc hebc)

/-- 既知区間と二つの未知 Hom から、元の全頂点上の native な豊穣関手を復元する。 -/
def finalHornFilledFunctor
    (hf : ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pathCubeBoundaryFace j).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontBoundaryFaceHom σ j)
    (hg : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up b)).ι ≫ g = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUpperCompositionHom σ b hb0 hbp)
    (hfg : f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastArrow σ) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornAppend n ≫ g) :
    EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n + 3)))) C where
  obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ X.as.down
  map X Y := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom σ g f X.as.down Y.as.down
  map_id X := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFillHom_id σ g f X.as.down
  map_comp X Y Z := finalHornFillHom_comp σ g f hf hg hfg X.as.down Y.as.down Z.as.down

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
