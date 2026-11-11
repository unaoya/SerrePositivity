module
public import SerrePositivity.KST.Spectra.PostMappingFibration
public import SerrePositivity.KST.Spectra.Limits.SpectrumMappingDiagram

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativePointedHomLifting

/-!
概要：段ごとの fibration に沿って持ち上がるスペクトル写像の整合族。
方針：零段は後合成の fibration、次段は単射な構造射に沿う相対ホーン充填を使う。
規約：L9 の実際の各段評価と厳密な構造条件を保持する。
使われ方：BF 1978 §2、HTT A.3.3、Sp の豊穣 Hom 写像の fibration 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
local instance spectrumHomHornFamilies_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 概要：段ごとの fibration に沿う Hom のホーンは各段で整合する族へ持ち上がる。
方針：後合成の初段の持ち上げから始め、構造射の単射性による相対持ち上げを反復する。
規約：ホーン上と底への合成の等式、構造射の整合条件を全て保持する。
使われ方：L9 の実際の Hom 空間の fibration の対角射を構成する。 -/
lemma spectrumHom_hornFamily (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (p : Y ⟶ Z) [∀ n, Fibration (p.app n).right]
    {T U : SSet.{u}} (j : T ⟶ U) (hj : J j)
    (a : T ⟶ OmegaSpectrum.mappingSpace X Y) (b : U ⟶ OmegaSpectrum.mappingSpace X Z)
    (h : a ≫ ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p =
      j ≫ b) :
    ∃ l : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right,
      (∀ n, j ≫ l n = a ≫ OmegaSpectrum.evaluation X Y n) ∧
      (∀ n, l n ≫ (PointedObject.basedHomMap (X.level n).space (p.app n)).right =
        b ≫ OmegaSpectrum.evaluation X Z n) ∧
      (∀ n, l (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
        l n ≫ OmegaSpectrum.mappingStep X Y n) := by
  let LiftAt (n : ℕ) := {l : U ⟶
      (PointedObject.basedHom (X.level n).space (Y.level n).space).right //
    j ≫ l = a ≫ OmegaSpectrum.evaluation X Y n ∧
      l ≫ (PointedObject.basedHomMap (X.level n).space (p.app n)).right =
        b ≫ OmegaSpectrum.evaluation X Z n}
  have h0 : Nonempty (LiftAt 0) := by
    have : HasLiftingProperty j
        (PointedObject.basedHomMap (X.level 0).space (p.app 0)).right :=
      ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance) j hj
    let sq : CommSq (a ≫ OmegaSpectrum.evaluation X Y 0) j
        (PointedObject.basedHomMap (X.level 0).space (p.app 0)).right
        (b ≫ OmegaSpectrum.evaluation X Z 0) := ⟨by
      rw [Category.assoc, ← spectrumHomMap_evaluation X (Y := Y) (Z := Z) p 0,
        ← Category.assoc, h, Category.assoc]⟩
    exact ⟨⟨sq.lift, sq.fac_left, sq.fac_right⟩⟩
  have hn (n : ℕ) (prev : LiftAt n) : ∃ next : LiftAt (n + 1),
      next.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
        prev.val ≫ OmegaSpectrum.mappingStep X Y n := by
    have hc : j ≫ (prev.val ≫ OmegaSpectrum.mappingStep X Y n) =
        (a ≫ OmegaSpectrum.evaluation X Y (n + 1)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space := by
      rw [← Category.assoc, prev.property.1, Category.assoc,
        ← OmegaSpectrum.evaluation_condition, ← Category.assoc]
    have he : (a ≫ OmegaSpectrum.evaluation X Y (n + 1)) ≫
        (PointedObject.basedHomMap (X.level (n + 1)).space (p.app (n + 1))).right =
          j ≫ (b ≫ OmegaSpectrum.evaluation X Z (n + 1)) := by
      rw [Category.assoc, ← spectrumHomMap_evaluation X (Y := Y) (Z := Z) p (n + 1),
        ← Category.assoc, h, Category.assoc]
    have ha : (prev.val ≫ OmegaSpectrum.mappingStep X Y n) ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (p.app (n + 1))).right =
          (b ≫ OmegaSpectrum.evaluation X Z (n + 1)) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Z.level (n + 1)).space := by
      change (prev.val ≫ OmegaSpectrum.mappingStep X Y n) ≫
          (pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (p.app (n + 1)) = _
      rw [Category.assoc, spectrumMappingStep_post X (Y := Y) (Z := Z) p n,
        ← Category.assoc]
      change (prev.val ≫ (PointedObject.basedHomMap (X.level n).space (p.app n)).right) ≫
        OmegaSpectrum.mappingStep X Z n = _
      rw [prev.property.2, Category.assoc, ← OmegaSpectrum.evaluation_condition,
        ← Category.assoc]
    obtain ⟨l, hl, hp, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativePointedHom_hornLift (X.sigma n) (p.app (n + 1)) j hj
      (a ≫ OmegaSpectrum.evaluation X Y (n + 1)) (prev.val ≫ OmegaSpectrum.mappingStep X Y n)
      (b ≫ OmegaSpectrum.evaluation X Z (n + 1)) hc he ha
    exact ⟨⟨l, hl, hb⟩, hp⟩
  let stage : ∀ n, LiftAt n := Nat.rec (Classical.choice h0) (fun n prev ↦ (hn n prev).choose)
  refine ⟨fun n ↦ (stage n).val, fun n ↦ (stage n).property.1,
    fun n ↦ (stage n).property.2, ?_⟩
  intro n
  exact (hn n (stage n)).choose_spec

end
end SerrePositivity.InfinityCategories.HomotopyLimits
