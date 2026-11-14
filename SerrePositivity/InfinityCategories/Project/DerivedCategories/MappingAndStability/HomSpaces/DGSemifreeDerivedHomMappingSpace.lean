module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeDerivedHomValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ComplexPinchedQuasiIso
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
/-- 共変 Hom の同じ分解複体の pinched 模型から、元の実写像空間への比較。 -/
def dgSemifreeDerivedHomMappingSpaceComparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v}
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomValue R D P Q).val.obj (Opposite.op PUnit.unit)) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) P Q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomAugmentation R D P Q) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomMappingSpaceIso R D P Q).inv
/-- 共変の同じ実 augmentation による、全写像空間の比較同値。 -/
theorem dgSemifreeDerivedHomMappingSpaceComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgSemifreeDerivedHomMappingSpaceComparison R D P Q) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomAugmentation_quasiIso R D P Q
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_trivialKanFibration.{u, max (u + 1) v}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomAugmentation R D P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomAugmentation_surjective R D P Q)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomAugmentation R D P Q))
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomMappingSpaceIso R D P Q).symm).isQCatEquivalence
  exact he.comp hi
/-- 同じ全 Kan 空間の比較は、実単体的ホモトピー同値でもある。 -/
lemma dgSemifreeDerivedHomMappingSpaceComparison_isSimplicialHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgSemifreeDerivedHomMappingSpaceComparison R D P Q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isSimplicialHomotopyEquivalence
    (dgSemifreeDerivedHomMappingSpaceComparison_isQCatEquivalence R D P Q)
/-- 反変 Hom の同じ分解複体から、元の同じ実写像空間への比較。 -/
def dgSemifreeDerivedHomSourceMappingSpaceComparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v}
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceValue R D P Q).val.obj (Opposite.op PUnit.unit)) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) P Q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceAugmentation R D P Q) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomMappingSpaceIso R D P Q).inv
/-- 反変の同じ実 augmentation から得る、全実写像空間の比較同値。 -/
theorem dgSemifreeDerivedHomSourceMappingSpaceComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgSemifreeDerivedHomSourceMappingSpaceComparison R D P Q) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceAugmentation_quasiIso R D P Q
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_trivialKanFibration.{u, max (u + 1) v}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceAugmentation R D P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceAugmentation_surjective R D P Q)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceAugmentation R D P Q))
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomMappingSpaceIso R D P Q).symm).isQCatEquivalence
  exact he.comp hi
end SerrePositivity.InfinityCategories.Project.DerivedCategories
