module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUpperActionValue
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUpperTriangleAction
public import SerrePositivity.InfinityCategories.F2.FunctorIsoDownHorizontal
public import SerrePositivity.InfinityCategories.F2.CoherentConstantTriangleLargeFactors
public import SerrePositivity.InfinityCategories.F2.CoherentNativeUnitValue

/-!
概要：既存の上面作用比較から、元の単位表現と native 作用の指定因子を取り出す。
方針：同じ単位表現の前合成と既存の native 作用比較を、同じ持ち上げ等式で揃える。
規約：指定比較を選び直さない。使われ方：二面比較と a6 の作用比較の共役式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "t" => coherentVertexOfHomotopy H
local notation "a" => coherentTransformationTotalMap F G t
local notation "z" => coherentDiagramTotalVertex G

/-- 元の native 作用比較の終点は、同じ具体的単位との合成の持ち上げ。 -/
lemma coherentColimitNativeAction_unit_lift :
    coherentLargeTotalUnit F ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (coherentTotalVertexMap F G a) =
      (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (a ≫ coherentDiagramTotalUnit G) := by
  change (_ ≫ (SSet.uliftFunctor.{u + 1, u}).map (coherentDiagramTotalUnit F)) ≫ _ = _
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, coherentTotalVertexMap_unit]

/-- 元の第二辺の指定単位表現を、同じ変換の全空間作用で前合成した因子。 -/
def coherentColimitUpperUnitFactorIso : FunctorIso (coherentColimitUpperCompositeAction B H)
    ((smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (a ≫ coherentDiagramTotalUnit G)) :=
  functorIsoOfEq ((coherentNativeUnitValueIso G).precomp
    (leftUnstraighteningMappingVertexMap F G t).val)
    rfl (coherentTransformationTotalMap_unit_lift F G t)

/-- 元の a6 の native 作用比較の逆を、同じ単位との合成の持ち上げで読む。 -/
def coherentColimitUpperNativeFactorIso : FunctorIso
    ((smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (a ≫ coherentDiagramTotalUnit G)) (coherentTotalMapNativeAction F G a) :=
  (functorIsoOfEq (coherentTotalMapNativeActionIso F G a) rfl
    (coherentColimitNativeAction_unit_lift B H)).symm

/-- 元の単位表現と元の native 作用比較だけから成る上面の外側の指定因子。 -/
def coherentColimitUpperTransportFactorIso :
    FunctorIso (coherentColimitUpperCompositeAction B H) (coherentTotalMapNativeAction F G a) :=
  coherentColimitUpperUnitFactorIso B H ≪≫ coherentColimitUpperNativeFactorIso B H

/-- 既存の上面作用比較は、同じ全上面の比較と元の外側の指定二因子の合成。 -/
lemma coherentColimitUpperActionIso_eq_triangle_transport :
    coherentColimitUpperActionIso B H =
      coherentColimitUpperTriangleActionIso B H ≪≫ coherentColimitUpperTransportFactorIso B H := by
  have he := coherentConstantTriangleLargeComparison_eq_factors F G z (coherentDiagramTotalUnit G)
    (coherentNativeUnitRepresentation G) t (coherentColimitNativeUnitTriangle B H)
    (coherentTransformationTotalMap_unit_lift F G t)
  have ht := congrArg (fun e => e ≪≫ coherentColimitUpperNativeFactorIso B H) he
  exact (coherentColimitUpperActionIso_eq_triangle B H
    (coherentColimitNativeAction_unit_lift B H)).trans
      (ht.trans (Iso.trans_assoc (coherentColimitUpperTriangleActionIso B H)
        (coherentColimitUpperUnitFactorIso B H) (coherentColimitUpperNativeFactorIso B H)))

end SerrePositivity.InfinityCategories.F2
