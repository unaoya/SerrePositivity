module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilies

/-!
概要：普遍錐の射の類は、元の図式へ制限した射の類で決まる。
方針：相対終対象の正次元境界充填を写像空間とホモトピー圏の充満忠実性へ移す。
規約：全極限の存在は要求しない。使われ方：指定 cospan の比較を保つ fiber 射の一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FiberCone

instance limitConesQuasicategory (K X : SSet.{u}) [Quasicategory X] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitCones K X) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

lemma relativeProjection_isFullyFaithful {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalProjection p) := by
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalVertices p : SSet.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_boundary_succ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalProjection_hasLiftingProperty_boundary p)

/-- 概要：普遍錐全体から図式への射影は写像空間で充満忠実。
方針：錐の制限の相対終対象の射影に一般補題を適用する。
規約：値域のみ quasicategory、図式の形状は任意。
使われ方：極限対象の射の比較。 -/
lemma projection_isFullyFaithful (K X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection K X) :=
  relativeProjection_isFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)

/-- 概要：普遍錐の射影は h 上で充満忠実な関手を与える。
方針：写像空間の充満忠実性を Hom の全単射へ移す。
規約：全ての図式の極限の存在は不要。
使われ方：普遍錐間の射の選択の比較。 -/
def projectionHoFullyFaithful (K X : SSet.{u}) [Quasicategory X] :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection K X)).toFunctor.FullyFaithful :=
  (projection_isFullyFaithful K X).toHoFullyFaithful

/-- 概要：普遍錐間の h の射は、図式へ射影した射が一致すれば等しい。
方針：h の射影関手の忠実性を使う。
規約：同じ二つの普遍錐を始点・終点とする射。
使われ方：図式の比較を固定した極限間の射の選択独立性。 -/
lemma projection_map_injective {K X : SSet.{u}} [Quasicategory X]
    {a b : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitCones K X)} {f g : a ⟶ b}
    (h : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection K X)).toFunctor.map f =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection K X)).toFunctor.map g) : f = g :=
  (projectionHoFullyFaithful K X).map_injective h


end SerrePositivity.KST.LocalizingInvariants.FiberCone
