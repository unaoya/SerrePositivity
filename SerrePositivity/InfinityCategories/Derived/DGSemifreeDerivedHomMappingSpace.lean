module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeDerivedHomValue
public import SerrePositivity.InfinityCategories.Derived.ComplexPinchedQuasiIso
/-!
概要：D(R) 値 Hom の実分解複体の pinched 空間を、元の実導来 ∞ 圏の写像空間へ比較する。
方針：同じ実 augmentation の全射準同型から自明 Kan fibration を得て、実 Hom end 比較同型を合成する。
規約：全 Kan 空間の同値であり、π₀ だけの比較ではない。使われ方：導来 Hom の実空間値との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (P Q : SemifreeDGModules R D)
/-- 共変 Hom の同じ分解複体の pinched 模型から、元の実写像空間への比較。 -/
def dgSemifreeDerivedHomMappingSpaceComparison :
    complexPinchedSpace.{u, max (u + 1) v}
      ((dgSemifreeDerivedHomValue R D P Q).val.obj (Opposite.op PUnit.unit)) ⟶
    DGNerve.pinchedHom R (SemifreeDGModules R D) P Q :=
  complexPinchedMap (dgSemifreeDerivedHomAugmentation R D P Q) ≫
    (dgSemifreeHomMappingSpaceIso R D P Q).inv
/-- 共変の同じ実 augmentation による、全写像空間の比較同値。 -/
theorem dgSemifreeDerivedHomMappingSpaceComparison_isQCatEquivalence :
    IsQCatEquivalence (dgSemifreeDerivedHomMappingSpaceComparison R D P Q) := by
  let := dgSemifreeDerivedHomAugmentation_quasiIso R D P Q
  let := complexPinchedMap_trivialKanFibration.{u, max (u + 1) v}
    (dgSemifreeDerivedHomAugmentation R D P Q)
    (dgSemifreeDerivedHomAugmentation_surjective R D P Q)
  have he := isQCatEquivalence_of_trivialKanFibration
    (complexPinchedMap.{u, max (u + 1) v} (dgSemifreeDerivedHomAugmentation R D P Q))
  have hi := (qCatEquivalenceOfIso (dgSemifreeHomMappingSpaceIso R D P Q).symm).isQCatEquivalence
  exact he.comp hi
/-- 同じ全 Kan 空間の比較は、実単体的ホモトピー同値でもある。 -/
lemma dgSemifreeDerivedHomMappingSpaceComparison_isSimplicialHomotopyEquivalence :
    IsSimplicialHomotopyEquivalence (dgSemifreeDerivedHomMappingSpaceComparison R D P Q) :=
  IsQCatEquivalence.isSimplicialHomotopyEquivalence
    (dgSemifreeDerivedHomMappingSpaceComparison_isQCatEquivalence R D P Q)
/-- 反変 Hom の同じ分解複体から、元の同じ実写像空間への比較。 -/
def dgSemifreeDerivedHomSourceMappingSpaceComparison :
    complexPinchedSpace.{u, max (u + 1) v}
      ((dgSemifreeDerivedHomSourceValue R D P Q).val.obj (Opposite.op PUnit.unit)) ⟶
    DGNerve.pinchedHom R (SemifreeDGModules R D) P Q :=
  complexPinchedMap (dgSemifreeDerivedHomSourceAugmentation R D P Q) ≫
    (dgSemifreeHomMappingSpaceIso R D P Q).inv
/-- 反変の同じ実 augmentation から得る、全実写像空間の比較同値。 -/
theorem dgSemifreeDerivedHomSourceMappingSpaceComparison_isQCatEquivalence :
    IsQCatEquivalence (dgSemifreeDerivedHomSourceMappingSpaceComparison R D P Q) := by
  let := dgSemifreeDerivedHomSourceAugmentation_quasiIso R D P Q
  let := complexPinchedMap_trivialKanFibration.{u, max (u + 1) v}
    (dgSemifreeDerivedHomSourceAugmentation R D P Q)
    (dgSemifreeDerivedHomSourceAugmentation_surjective R D P Q)
  have he := isQCatEquivalence_of_trivialKanFibration
    (complexPinchedMap.{u, max (u + 1) v} (dgSemifreeDerivedHomSourceAugmentation R D P Q))
  have hi := (qCatEquivalenceOfIso (dgSemifreeHomMappingSpaceIso R D P Q).symm).isQCatEquivalence
  exact he.comp hi
end SerrePositivity.InfinityCategories
