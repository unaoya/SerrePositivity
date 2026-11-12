module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeUnitCapPastingEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeUnitCollarIntervalTriangle
/-! # 同じ導来写像空間内の係数側六三角形

概要：六片を両端固定で curry し、共有辺と二つの実単位補正対角を写像空間内で保持する。
方針：同じ四面体の実評価と区間 uncurry の単射性を使う。
規約：六二単体と二補正道の代表を変更しない。
使われ方：係数 path を含む高次合成関係を、補正対角の合成三角形へ貼り合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativeUnitCapIntervalTriangle (i : Fin 6) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y i)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_source R C D M X Y i)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_target R C D M X Y i)

lemma dgGluingNativeUnitCapIntervalTriangle_evaluate (i : Fin 6) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingNativeUnitCapIntervalTriangle R C D M X Y i) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints _ _ _

lemma dgGluingNativeUnitCapIntervalTriangle_first_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 0 =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 1 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_first_diagonal R C D M X Y

lemma dgGluingNativeUnitCapIntervalTriangle_last_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 2 =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 3 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_last_diagonal R C D M X Y

lemma dgGluingNativeUnitCapIntervalTriangle_first_bridge :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 1 =
      (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 5 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_first_bridge R C D M X Y

lemma dgGluingNativeUnitCapIntervalTriangle_last_bridge :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 3 =
      (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 5 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_last_bridge R C D M X Y

lemma dgGluingNativeUnitCapIntervalTriangle_coefficient_first :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 1 =
      (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 4 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_coefficient_first R C D M X Y

lemma dgGluingNativeUnitCapIntervalTriangle_coefficient_last :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 3 =
      (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 4 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_coefficient_last R C D M X Y

lemma dgGluingNativeUnitCapIntervalTriangle_collar_bridge :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 5 =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarIntervalTriangle R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    dgGluingNativeUnitCapIntervalTriangle_evaluate R C D M X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarIntervalTriangle_evaluate R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_collar_bridge R C D M X Y

lemma dgGluingNativeUnitCapIntervalTriangle_first_cap :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 0 =
      (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath R C D M X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgGluingNativeUnitCapIntervalTriangle_evaluate,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_first_cap R C D M X Y

lemma dgGluingNativeUnitCapIntervalTriangle_last_cap :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 2 =
      (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath R C D M X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgGluingNativeUnitCapIntervalTriangle_evaluate,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily_last_cap R C D M X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
