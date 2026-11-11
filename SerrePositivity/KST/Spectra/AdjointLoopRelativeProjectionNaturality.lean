module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeFullGradedInclusion

/-!
概要：相対 BF の元の右射影を保つ全 Hom の段ごとの豊穣自然変換。
方針：同じ二境界引き戻しの右条件と実 loop の豊穣作用を束ねる。
規約：左因子と同じ組の全パラメータを使い、右射影を選び直さない。
使われ方：指定単位の厳密な回収と補助 loop 列の全図式比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance adjointLoopRelativeProjectionNaturalityLocal1 : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance adjointLoopRelativeProjectionNaturalityLocal2 : SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 概要：実置換の段評価は全 Hom 上の単体的豊穣関手。
方針：元の BF 段評価と実射影の単位・合成保存を使う。
規約：指定した相対 BF 対象を評価する。
使われ方：元の右射影の始域。 -/
def fullMiddleStageEnriched (n : ℕ) :
    EnrichedFunctor SSet.{u} FullObject PointedSimplicialSet.{u} where
  obj X := ((middle X.val).level n).space
  map X Y := fullReplacedStage X.val Y.val n
  map_id X := by
    change fullCompatibleIdentity X.val ≫
      (fullReplacedMap X.val X.val ≫ evaluation (middle X.val) (middle X.val) n) = _
    rw [← Category.assoc, fullCompatibleIdentity_replacedMap, mappingIdentity_evaluation]
  map_comp X Y Z := by
    change fullCompatibleComposition X.val Y.val Z.val ≫
      (fullReplacedMap X.val Z.val ≫ evaluation (middle X.val) (middle Z.val) n) = _
    rw [← Category.assoc, fullCompatibleComposition_replacedMap]
    exact fullReplacedStage_composition X.val Y.val Z.val n

/-- 概要：補助 loop 列の段の全 Hom 作用も実豊穣関手。
方針：元の段評価に内部 Hom の実豊穣関手を適用する。
規約：同じ元の射を次段で評価する。
使われ方：指定右射影の終域。 -/
def fullTargetStageEnriched (n : ℕ) :
    EnrichedFunctor SSet.{u} FullObject PointedSimplicialSet.{u} where
  obj X := ((target X.val).level n).space
  map X Y := fullOriginalLoopStage X.val Y.val n
  map_id X := by
    change fullCompatibleIdentity X.val ≫
      (fullOriginalMap X.val X.val ≫ evaluation X.val X.val (n + 1) ≫
        (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map
          (X.val.level (n + 1)).space (X.val.level (n + 1)).space) = _
    rw [← Category.assoc, fullCompatibleIdentity_originalMap, mappingIdentity_evaluation_assoc]
    have h := (PointedMapping.ihomSimplicialFunctor
      PointedSimplicialSet.circle.{u}).map_id (X.val.level (n + 1)).space
    exact h.trans (by
      simp only [target, KanSequence.adjointLoop, KanSequence.mapping, KanSequence.tail,
        PointedObject.ihom_obj_eq_basedHom, PointedMapping.ihomSimplicialFunctor]
      rfl)
  map_comp X Y Z := by
    change fullCompatibleComposition X.val Y.val Z.val ≫
      (fullOriginalMap X.val Z.val ≫ evaluation X.val Z.val (n + 1) ≫
        (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map
          (X.val.level (n + 1)).space (Z.val.level (n + 1)).space) = _
    rw [← Category.assoc, fullCompatibleComposition_originalMap]
    exact fullOriginalLoopStage_composition X.val Y.val Z.val n

/-- 概要：元の右射影は各段で全 Hom 上の厳密な豊穣自然変換。
方針：同じ二境界引き戻しの右条件を豊穣正方形へ移す。
規約：元の右射影と左因子を同時に保持する。
使われ方：補助 loop の実相対 BF 置換の全図式自然性。 -/
def fullGradedProjection (n : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (fullMiddleStageEnriched n) (fullTargetStageEnriched n) where
  app X := eHomEquiv SSet ((projection X.val).app n)
  naturality X Y := ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff SSet
    ((projection X.val).app n) ((projection Y.val).app n)
    (fullOriginalLoopStage X.val Y.val n) (fullReplacedStage X.val Y.val n)).mp
      (full_right_whiskered X.val Y.val n)).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
