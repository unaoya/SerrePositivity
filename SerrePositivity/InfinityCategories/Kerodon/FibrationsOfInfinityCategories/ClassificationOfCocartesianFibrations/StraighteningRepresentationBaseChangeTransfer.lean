module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StraighteningRepresentationComparisonLaw
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange

/-!
概要：同じ表現空間の比較に沿って、指定分類比較の底変換の可換式を移す。
方針：既存 representationIso と cartesianRestrict_diagramIso の合成則を使う。
規約：Kerodon §5.6（Tag 027M）、HTT §3.3.2 の既存構成の法則。
  第3項全体の底変換可換式の証明の分割であり、その無条件の結論ではない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
local instance representationBaseChangeTransfer_left {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
 LeftFibration (pullback.snd p k) := ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 指定底変換の可換式は、同じ表現空間内の比較に沿って移る。
元の底変換同型を変更せず、可換式が分かっている表現からもう一つの表現へ渡す合成則。 -/
lemma leftStraighteningInfinityDiagram_representationIso_baseChange_transfer {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B)
    (R S : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p))
    (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))
    (h : leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
       leftStraighteningInfinityDiagram_representationIso (pullback.snd p k) (R.nativeRestrict k) =
      (leftStraighteningInfinityDiagram_representationIso p R).precomp
        ((SSet.uliftFunctor.{u+1,u}).map k)) :
    leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
       leftStraighteningInfinityDiagram_representationIso (pullback.snd p k) (S.nativeRestrict k) =
      (leftStraighteningInfinityDiagram_representationIso p S).precomp
        ((SSet.uliftFunctor.{u+1,u}).map k) := by
 let a' := R.cartesianRestrictVertexIso S a
   ((SSet.uliftFunctor.{u+1,u}).map (pullback.fst p k))
   ((SSet.uliftFunctor.{u+1,u}).map k) (ulift_isPullback p k)
 have hc := R.cartesianRestrict_diagramIso S a
   ((SSet.uliftFunctor.{u+1,u}).map (pullback.fst p k))
   ((SSet.uliftFunctor.{u+1,u}).map k) (ulift_isPullback p k)
 have ht := leftStraighteningInfinityDiagram_representationIso_comp_diagramIso
   (pullback.snd p k) (R.nativeRestrict k) (S.nativeRestrict k) a'
 rw [← ht, ← leftStraighteningInfinityDiagram_representationIso_comp_diagramIso p R S a,
   functorIso_precomp_trans, ← hc, ← Iso.trans_assoc, h]
 rfl
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
