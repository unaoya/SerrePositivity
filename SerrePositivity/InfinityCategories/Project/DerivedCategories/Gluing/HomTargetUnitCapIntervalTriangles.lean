module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCollarIntervalTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCapPastingEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCollarIntervalTriangle
/-!
概要：元終域の六片を端点固定で curry し、全共有辺と実 cap 対角を保持する。
方針：元の全入力・指定面・全区間族を保持する比較を合成する。
規約：追加の主経路仮定を置かない。使われ方：元 lax Hom 比較の逆の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetUnitCapIntervalTriangle (i : Fin 6) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y i)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_source R C D E p q X Y i)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_target R C D E p q X Y i)

lemma dgGluingHomTargetUnitCapIntervalTriangle_evaluate (i : Fin 6) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y i) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints _ _ _

lemma dgGluingHomTargetUnitCapIntervalTriangle_first_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 0 =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 1 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_first_diagonal R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_last_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 2 =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 3 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_last_diagonal R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_first_bridge :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 1 =
      (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 5 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_first_bridge R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_last_bridge :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 3 =
      (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 5 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_last_bridge R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_coefficient_first :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 1 =
      (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 4 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_first R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_coefficient_last :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 3 =
      (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 4 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_last R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_collar_bridge :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 5 =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarIntervalTriangle R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarIntervalTriangle_evaluate R C D E p q X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_collar_bridge R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_first_cap :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 0 =
      (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgGluingHomTargetUnitCapIntervalTriangle_evaluate,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_first_cap R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_last_cap :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 2 =
      (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgGluingHomTargetUnitCapIntervalTriangle_evaluate,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily_last_cap R C D E p q X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
