module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationRightKanShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeUniverseNaturality

/-!
概要：篩の二段分解の三角形から、元の係数前層での指定右 Kan 輸送を固定する。
方針：元の自然変換を AsSmall へ写し、既存の nerve の輸送に同じ係数射を後合成する。
使われ方：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の降下の合成。
規約：局所極限性は後続で証明する。余単位や局所輸送を点ごとに選び直さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 中間射の始域の図式を、係数と同じ上の universe へ移す。 -/
abbrev sieveFactorizationRightKanTarget (R : Sieve U) :=
  asSmallLocalFunctor (sieveDiagram R)

/-- 合成射の最初の始域の図式を、同じ上の universe へ移す。 -/
abbrev sieveFactorizationRightKanSource (R S : Sieve U) :=
  asSmallLocalFunctor (sieveFactorizationDiagram R S)

/-- 指定余単位は、元の二段分解の三角形そのものである。 -/
def sieveFactorizationRightKanCounit (R S : Sieve U) :
    sieveFactorizationRightKanFunctor R S ⋙ sieveFactorizationRightKanTarget R ⟶
      sieveFactorizationRightKanSource R S :=
  Functor.whiskerLeft AsSmall.down (Functor.whiskerRight (sieveFactorizationTriangle R S) AsSmall.up)

variable {E : SSet.{u + 1}}

/-- 元の係数前層を同じ AsSmall nerve の表示へ移す。係数の universe は保つ。 -/
abbrev sieveFactorizationRightKanCoefficient (F : Presheaf C E) :
    nerve (AsSmall.{u + 1} Cᵒᵖ) ⟶ E :=
  (nerveAsSmallIso Cᵒᵖ).inv ≫ F

/-- 指定余単位を、元の係数前層へ写した同じ自然変換の円柱。 -/
abbrev sieveFactorizationRightKanCounitHomotopy (R S : Sieve U) (F : Presheaf C E) :=
  kanRightCounitPostcomp
    (δ := nerveMap (sieveFactorizationRightKanFunctor R S))
    (F := nerveMap (sieveFactorizationRightKanTarget R))
    (F₀ := nerveMap (sieveFactorizationRightKanSource R S))
    (nerveNatTransHomotopy (sieveFactorizationRightKanCounit R S))
    (sieveFactorizationRightKanCoefficient F)

/-- 各点の指定右 Kan 輸送は、元の三角形の実輸送の同じ後合成。 -/
abbrev sieveFactorizationRightKanTransport (R S : Sieve U) (t : sieveCategory R)
    (F : Presheaf C E) :=
  nerveRightConeTransportPostcomp (sieveFactorizationRightKanFunctor R S)
    (sieveFactorizationRightKanCounit R S) (AsSmall.up.obj (Opposite.op t))
      (sieveFactorizationRightKanCoefficient F)

/-- 元の通常の局所形状へ制限した全錐の値を、そのまま回収する。 -/
lemma sieveFactorizationRightKanTransport_local_val (R S : Sieve U) (t : sieveCategory R)
    (F : Presheaf C E) :
    (SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone
      (sieveFactorizationRightKanTransport R S t F).cone
      (nerveRightKanShapeIso (AsSmall.up.obj (Opposite.op t))
        (sieveFactorizationRightKanFunctor R S)).hom).val =
      ((SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone
        ((Functor.RightExtension.mk (sieveFactorizationRightKanTarget R)
          (sieveFactorizationRightKanCounit R S)).coneAt (AsSmall.up.obj (Opposite.op t)))).postcomp
            (sieveFactorizationRightKanCoefficient F)).val :=
  nerveRightConeTransportPostcomp_cone_val _ _ _ _

end SerrePositivity.InfinityCategories.Sheaves
