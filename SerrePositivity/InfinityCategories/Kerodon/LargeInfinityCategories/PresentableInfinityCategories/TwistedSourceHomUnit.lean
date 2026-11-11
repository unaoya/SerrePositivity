module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CosliceTwistedArrowNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ClassifiedSquareHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CosliceLeftKanHomUniversal
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SourceInitial

/-!
概要：始点固定 twisted arrow の元の後合成を分類した指定単位の全 Hom 普遍性。
方針：元の coslice 単位との厳密な実正方形を分類し、同じ実比較の可逆性で移す。
規約：元の後合成射と指定底変換同型を保持する。
使われ方：P-12 の共同 Hom 比較の始点固定評価の普遍性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：点の射で指定した元の coslice 比較は前合成同値。
方針：点を元の頂点で表示して既存の同値性を使う。
規約：元の比較射自身の性質。使われ方：指定分類射の可逆性の判定。 -/
lemma pointCosliceToTwistedArrowSource_isPrecompositionEquivalence
    {A : SSet.{u}} [Quasicategory A] (p : (Δ[0] : SSet.{u}) ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointCosliceToTwistedArrowSource p) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder
    (Equiv.symm_apply_apply (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) p).symm))).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_isPrecompositionEquivalence (SSet.yonedaEquiv p))

variable {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (p : (Δ[0] : SSet.{u}) ⟶ A)

/-- 概要：元の始点固定 twisted arrow の後合成を分類した指定 Hom 単位。
方針：元の全空間の後合成を実 pullback へ持ち上げて分類する。
規約：元の F と固定点 p を使う。使われ方：共同 Hom 比較の始点固定模型。 -/
def twistedSourceHomUnit :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv p)))
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv (p ≫ F)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationSquareHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv (p ≫ F))) F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedArrowSourcePostcomp F (SSet.yonedaEquiv p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedArrowSourcePostcomp_projection F (SSet.yonedaEquiv p))

/-- 概要：点の射で指定した元の coslice 後合成の分類単位は左 Kan Hom 普遍性を持つ。
方針：点を元の頂点へ戻し、完成した指定 coslice 単位の普遍性を使う。
規約：元の全空間の後合成を保持する。使われ方：始点固定単位への移送の始点。 -/
lemma pointCosliceSquareHom_homUniversal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal ((SSet.uliftFunctor.{u + 1, u}).map F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationSquareHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (p ≫ F))
        F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection p F)) := by
  obtain ⟨a, rfl⟩ := (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)).symm.surjective p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.classifiedCosliceLeftKanUnit_homUniversal F a

/-- 概要：元の始点固定 twisted arrow の指定後合成単位は左 Kan Hom 普遍性を持つ。
方針：実 coslice 比較の分類射を同型とし、厳密な実正方形の分類の自然性で移す。
規約：元の単位自身の普遍性を結論する。
使われ方：共同 Hom 単位の始点固定評価から指定 Yoneda 単位の普遍性への接続。 -/
lemma twistedSourceHomUnit_homUniversal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal ((SSet.uliftFunctor.{u + 1, u}).map F) (twistedSourceHomUnit F p) := by
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointCosliceToTwistedArrowSource p
  let hv := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointCosliceToTwistedArrowSource_projection p
  let w := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointCosliceToTwistedArrowSource (p ≫ F)
  let hw := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointCosliceToTwistedArrowSource_projection (p ≫ F)
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv p)) v hv) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom_isIso_of_precompositionEquivalence _ _ v hv
      (pointCosliceToTwistedArrowSource_isPrecompositionEquivalence p)
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (p ≫ F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv (p ≫ F))) w hw) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom_isIso_of_precompositionEquivalence _ _ w hw
      (pointCosliceToTwistedArrowSource_isPrecompositionEquivalence (p ≫ F))
  let ev := asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv p)) v hv)
  let ew := asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (p ≫ F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv (p ≫ F))) w hw)
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationSquareHom_naturality
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (p ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv (p ≫ F)))
    F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection p F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedArrowSourcePostcomp F (SSet.yonedaEquiv p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedArrowSourcePostcomp_projection F (SSet.yonedaEquiv p)) v hv w hw
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointCosliceToTwistedArrowSource_postcomp F p)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKanHomUniversal_of_unit_iso_square _ _ _ (pointCosliceSquareHom_homUniversal F p) ev ew
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv p)) v hv ≫ twistedSourceHomUnit F p =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationSquareHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (p ≫ F))
      F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection p F) ≫
        (hoFunctor.map ((MonoidalClosed.pre ((SSet.uliftFunctor.{u + 1, u}).map F)).app
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).toFunctor.map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (p ≫ F))
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv (p ≫ F))) w hw)
  simpa only [twistedSourceHomUnit, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap,
    eqToHom_refl, Category.id_comp, Category.comp_id] using hn

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
