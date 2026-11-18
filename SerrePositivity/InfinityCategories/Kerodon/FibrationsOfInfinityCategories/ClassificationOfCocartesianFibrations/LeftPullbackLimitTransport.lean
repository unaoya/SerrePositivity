module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningLimitTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseMorphismUp

/-!
概要：指定した同型な底写像による left fibration の引き戻しは同じ係数の極限の存在を保つ。
方針：実際の共同分類の底変換同型と、元の関手同型の持ち上げを合成する。
規約：係数は元の同じ底の図式で、引き戻し写像の単射性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、Definition 7.3.1.2（Tag 02Y9）、
S8 の固定 Yoneda の右 Kan 局所図式の底移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {E B K X : SSet.{u}} [Quasicategory B] [Quasicategory K] [Quasicategory X]
  (p : E ⟶ B) [LeftFibration p] {f g : K ⟶ B}

local instance leftPullbackLimitTransport_projection (a : K ⟶ B) : LeftFibration (pullback.snd p a) :=
  ⟨leftFibrations.pullback_snd p a (LeftFibration.mem (p := p))⟩

/-- 元の底写像の指定同型は、引き戻しの全分類図式の同じ関手同型を与える。
Kerodon Corollary 5.6.0.6（Tag 028T）、共同分類の底変換と係数移送の合成則。 -/
def leftPullbackClassificationIso (e : FunctorIso f g) :
    FunctorIso (leftStraighteningInfinityDiagram (pullback.snd p f))
      (leftStraighteningInfinityDiagram (pullback.snd p g)) :=
  (leftStraighteningInfinityDiagram_baseChangeIso p f).symm ≪≫
    (functorIso_ulift.{u, u + 1} e).postcomp (leftStraighteningInfinityDiagram p) ≪≫
      leftStraighteningInfinityDiagram_baseChangeIso p g

/-- 同型な底写像の引き戻しの上で、元の同じ係数の極限の存在を双方向に移す。
Kerodon Corollary 5.6.0.6（Tag 028T）、Definition 7.3.1.2（Tag 02Y9）、
既存の共同分類と復元比較に沿う底移送の法則。 -/
lemma hasLimit_leftPullback_iff_of_functorIso (e : FunctorIso f g) (O : K ⟶ X) :
    HasLimit (pullback.snd p f ≫ O) ↔ HasLimit (pullback.snd p g ≫ O) :=
  hasLimit_iff_of_leftStraighteningIso (pullback.snd p f) (pullback.snd p g)
    (leftPullbackClassificationIso p e) O

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
