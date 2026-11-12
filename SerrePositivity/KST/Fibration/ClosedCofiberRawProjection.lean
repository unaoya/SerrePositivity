module
public import SerrePositivity.KST.Fibration.ClosedFlagCofiberCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：閉じた P cofiber の全補完から元の全矢印図式への充満忠実な実射影。
方針：同じ trivial Kan 射影と元の完全な全部分圏包含を合成する。
規約：商の核表示なし。使われ方：元の包含に沿う cofiber 係数の全関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B)

/-- 概要：全 P 相対 cofiber 補完の元の実底辺射影。
方針：同じ実 cofiber 射影から全部分矢印圏の包含を合成する。
規約：元の全矢印図式が行先。使われ方：元の二補完の共通比較底。 -/
def closedCofiberRawProjection :
    (relativeCofiberStableModel (ClosedStablePredicate.top B) P).carrier ⟶
      (ihom (Δ[1] : SSet.{u})).obj B.carrier :=
  closedCofiberProjection P ≫ (closedStableInclusion (closedArrowPredicate P)).val

/-- 概要：全 P 補完の元の実底辺射影は native 写像空間で充満忠実。
方針：同じ trivial Kan 射影と全部分圏包含の充満忠実性を合成する。
規約：商・分数 API を新設しない。使われ方：二つの共通補完の全族比較。 -/
theorem closedCofiberRawProjection_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (closedCofiberRawProjection P) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration (closedCofiberProjection P)).comp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ (closedArrowPredicate P).predicate)

/-- 概要：元の実底辺射影は同じ全 cofiber 図式の底辺そのもの。
方針：元の全部分圏制限の厳密包含公式を消費する。
規約：同じ補完を保持。使われ方：完全関手による実後合成の自然性。 -/
theorem closedCofiberRawProjection_inclusion :
    closedCofiberRawProjection P =
      (relativeCofiberInclusion (ClosedStablePredicate.top B) P).val ≫
        cofiberProjection B.carrier :=
  fullPredicateMap_ι _ _ _ _

/-- 概要：全旗の共通補完の実底辺は元の実合成辺制限。
方針：同じ補完切断の回収と元の辺抽出の包含公式を合成する。
規約：全自然変換の厳密回収。使われ方：元の包含による cofiber 比較の底面。 -/
theorem closedFlagCofiberCompletion_rawProjection {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    (closedFlagCofiberCompletion P α).val ≫ closedCofiberRawProjection P =
      (closedStableInclusion (closedFlagStablePredicate P n)).val ≫
        (pre (stdSimplex.map α)).app B.carrier := by
  change ((closedFlagCofiberCompletion P α ≫ (closedArrowCofiberEquivalence P).hom) ≫
    closedStableInclusion (closedArrowPredicate P)).val = _
  rw [closedFlagCofiberCompletion_projection]
  exact congrArg (fun f => f.val) (closedFlagEdge_inclusion P α)

end SerrePositivity.KST.Fibration
