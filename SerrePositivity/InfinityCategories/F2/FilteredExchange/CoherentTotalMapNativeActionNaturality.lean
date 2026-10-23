module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalMapNativeActionComponents
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCoconeTransportActionNaturality

/-!
概要：元の native 作用比較の同じ二成分の合成へ、全 Hom の指定自然性を移す。
方針：元の全 Hom 比較と指定余錐比較の正方形を合成する。
規約：native な射・指定比較・同型を保持。使われ方：上側 native 因子の三角形整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a b : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)
local notation "z" => coherentDiagramTotalVertex G
local notation "x" => Sigma.fst (coherentTotalMapNativeRepresentation F G a)
local notation "y" => Sigma.fst (coherentTotalMapNativeRepresentation F G b)
local notation "S" => Iso.inv (smallUnstraighteningHomIso F (KanObject.obj (spaceInfinityObject z)))
local notation "L" => (coconePointHomFamily (coherentDiagramTotalCocone F) z ≫
  coherentCoconeTotalComparison F z) ≫ S
local notation "u₀" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F G a) S)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a))
local notation "u₁" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F G b) S)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G b))

/-- 同じ指定余錐比較の正方形から、元の native 作用比較の同じ二成分の自然性を得る。 -/
lemma coherentTotalMapNativeActionComponentsIso_naturality (n : VertexIso x y)
    (m : VertexIso
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a)))
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G b))))
    (hu : u₀ ≪≫ m = VertexIso.map n L ≪≫ u₁) :
    coherentTotalMapNativeActionComponentsIso F G a ≪≫ m =
      VertexIso.map n (coherentCoconeTransportAction F (coherentDiagramTotalCocone F) z) ≪≫
        coherentTotalMapNativeActionComponentsIso F G b := by
  exact functorIso_app_vertexIso_comparison_naturality
    (coherentCoconeTransportActionIso F (coherentDiagramTotalCocone F) z) n u₀ u₁ m hu

/-- 同じ指定余錐比較の正方形は、元の上側 native 因子を表す同じ逆の自然性を与える。 -/
lemma coherentTotalMapNativeActionComponentsIso_inverse_naturality (n : VertexIso x y)
    (m : VertexIso
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a)))
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G b))))
    (hu : u₀ ≪≫ m = VertexIso.map n L ≪≫ u₁) :
    m ≪≫ (coherentTotalMapNativeActionComponentsIso F G b).symm =
      (coherentTotalMapNativeActionComponentsIso F G a).symm ≪≫
        VertexIso.map n (coherentCoconeTransportAction F (coherentDiagramTotalCocone F) z) := by
  exact functorIso_app_vertexIso_comparison_inverse_naturality
    (coherentCoconeTransportActionIso F (coherentDiagramTotalCocone F) z) n u₀ u₁ m hu

end SerrePositivity.InfinityCategories.F2
