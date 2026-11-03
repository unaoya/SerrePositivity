module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceLongOldData
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceLongComposition

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
  {F G J Q₀ Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k

/-- 普遍長辺と指定三角形の長辺を、既存の指定比較と同じデータの表示へ移す。 -/
def coherentColimitUnitZeroFaceOldLongWitness (original : Bool) :=
  let wSource := if original then coherentColimitUnitZeroFaceLongWitness B T k H he S hS true
    else coherentColimitUnitZeroFaceCanonicalLongWitness B T k H he S hS
  wSource.transportData (coherentColimitUnitZeroFaceLong_old_base B T k H he S hS)
    (coherentColimitUnitZeroFaceLong_old_initial B T k H he)
    (coherentColimitUnitZeroFaceLong_old_apex B T k H he)

/-- 元の既存の底・初期値・終点底の表示による、同じ普遍長辺からの直接比較。 -/
def coherentColimitUnitZeroFaceOldLongIso :=
  (coherentColimitUnitZeroFaceOldLongWitness B T k H he S hS false).iso
    (coherentColimitUnitZeroFaceOldLongWitness B T k H he S hS true)
    (prismEndpoint_zero_leftAnodyne (leftUnstraightening F ⊗ K))
    (coherentColimitUnitZeroFaceOldLongWitness B T k H he S hS true).initial_base
    (coherentColimitUnitZeroFaceOldLongWitness B T k H he S hS true).endpoint_base

/-- 直接比較の同じ実延長・実終点を保つ表示変更は、元の指定同型の値を変えない。 -/
lemma coherentColimitUnitZeroFaceLongCompositeIso_heq_old :
    HEq (coherentColimitUnitZeroFaceLongCompositeIso B T k H he S hS)
      (coherentColimitUnitZeroFaceOldLongIso B T k H he S hS) :=
  RelativeExtensionEndpointWitness.iso_heq_of_dataEq
    (coherentColimitUnitZeroFaceCanonicalLongWitness B T k H he S hS)
    (coherentColimitUnitZeroFaceLongWitness B T k H he S hS true)
    (coherentColimitUnitZeroFaceOldLongWitness B T k H he S hS false)
    (coherentColimitUnitZeroFaceOldLongWitness B T k H he S hS true)
    (coherentColimitUnitZeroFaceLong_old_base B T k H he S hS)
    (coherentColimitUnitZeroFaceLong_old_initial B T k H he)
    (coherentColimitUnitZeroFaceLong_old_apex B T k H he) rfl rfl rfl rfl
    (prismEndpoint_zero_leftAnodyne (leftUnstraightening F ⊗ K))
    (coherentColimitUnitZeroFaceLong_base_initial B T k H he S hS)
    (coherentColimitUnitZeroFaceOldLongWitness B T k H he S hS true).initial_base
    (coherentColimitUnitZeroFaceLong_base_endpoint B T k H he S hS)
    (coherentColimitUnitZeroFaceOldLongWitness B T k H he S hS true).endpoint_base

end SerrePositivity.InfinityCategories.F2
