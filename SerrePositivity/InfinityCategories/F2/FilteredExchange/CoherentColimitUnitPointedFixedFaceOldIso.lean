module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceOldData
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceLongComposition

/-!
概要：長辺三証拠の直接比較を、既存の指定三角形比較と同じ底・全初期値の表示へ移す。
方針：同じ実延長・実終点のまま三つのデータの等式を渡す。
規約：指定同型の値を保持。使われ方：既存の指定三角形比較の前合成への最終照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k

/-- 普遍長辺と指定三角形の長辺を、既存の指定比較と同じデータの表示へ移す。 -/
def coherentColimitUnitPointedFixedFaceOldLongWitness (original : Bool) :=
  let wSource := if original then
    coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS true
    else coherentColimitUnitPointedFixedFaceCanonicalLongWitness B T k j hj S hS
  wSource.transportData (coherentColimitUnitPointedFixedFaceLong_old_base B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceLong_old_initial B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceLong_old_apex B T k)

/-- 元の既存の底・初期値・終点底の表示による、同じ普遍長辺からの直接比較。 -/
def coherentColimitUnitPointedFixedFaceOldLongIso :=
  (coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS false).iso
    (coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS true)
    (prismEndpoint_zero_leftAnodyne (leftUnstraightening F ⊗ K))
    (coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS true).initial_base
    (coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS true).endpoint_base

/-- 直接比較の同じ実延長・実終点を保つ表示変更は、元の指定同型の値を変えない。 -/
lemma coherentColimitUnitPointedFixedFaceLongCompositeIso_heq_old :
    HEq (coherentColimitUnitPointedFixedFaceLongCompositeIso B T k j hj S hS)
      (coherentColimitUnitPointedFixedFaceOldLongIso B T k j hj S hS) :=
  RelativeExtensionEndpointWitness.iso_heq_of_dataEq
    (coherentColimitUnitPointedFixedFaceCanonicalLongWitness B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS true)
    (coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS false)
    (coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS true)
    (coherentColimitUnitPointedFixedFaceLong_old_base B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceLong_old_initial B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceLong_old_apex B T k) rfl rfl rfl rfl
    (prismEndpoint_zero_leftAnodyne (leftUnstraightening F ⊗ K))
    (coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS false).initial_base
    (coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS true).initial_base
    (coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS false).endpoint_base
    (coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS true).endpoint_base

end SerrePositivity.InfinityCategories.F2
