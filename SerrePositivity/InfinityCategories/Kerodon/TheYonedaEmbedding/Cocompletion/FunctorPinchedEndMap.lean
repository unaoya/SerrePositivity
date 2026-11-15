module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwistedHomEndSection
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SourceInitial
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence

/-!
概要：元の pinched Hom から同じ end 係数の切断空間への射を固定する。
方針：既存の左右 Hom 比較と恒等点からの輸送を、元の end 比較へ合成する。
規約：end 比較の同値性を仮定・主張しない。全パラメーターで同じ射を使う。
使われ方：E06 の射の構成、RR04 の全族の三角形。
対応：Kerodon Tag 03JV、HTT §1.2.2 の写像空間模型と 3.3.3.4 の切断表示に関係する比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion

/-- 同じ左右 Hom 比較と恒等点輸送を通じた、元の end 切断への射。
同値性は別項目 E06 に残す。 -/
def functorPinchedEndMap {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    pinchedHom (functorVertex F) (functorVertex G) ⟶
      simplicialSections (functorEndProjection F G) :=
  (pinchedHomLeftRightEquivalence (functorVertex F) (functorVertex G)).symm.hom ≫
    twistedArrowIdentityHomTransport (functorVertex F) (functorVertex G) ≫
      twistedFunctorHomToEndSections F G

/-- 元の end 比較による切断の評価式を、同じ pinched 比較の全族へ制限する。 -/
lemma functorPinchedEndMap_evaluation {A C : SSet.{u}} [Quasicategory C]
    (F G : A ⟶ C) :
    (TwistedArrow A ◁ functorPinchedEndMap F G) ≫
      simplicialSectionsEvaluation (functorEndProjection F G) =
    (TwistedArrow A ◁ ((pinchedHomLeftRightEquivalence
      (functorVertex F) (functorVertex G)).symm.hom ≫
        twistedArrowIdentityHomTransport (functorVertex F) (functorVertex G))) ≫
      twistedFunctorHomEndEvaluation F G := by
  simp only [functorPinchedEndMap, whiskerLeft_comp, Category.assoc,
    twistedFunctorHomToEndSections_evaluation]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
