module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCollarIntervalTriangle
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapPastingEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCollarIntervalTriangle
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetUnitCapIntervalTriangle (i : Fin 6) :=
  intervalMappingCurryOfEndpoints (dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y i)
    (dgGluingHomTargetUnitCapPastingTriangleFamily_source R C D E p q X Y i)
    (dgGluingHomTargetUnitCapPastingTriangleFamily_target R C D E p q X Y i)

lemma dgGluingHomTargetUnitCapIntervalTriangle_evaluate (i : Fin 6) :
    intervalMappingUncurry (dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y i) =
      dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y i :=
  intervalMappingUncurry_curryOfEndpoints _ _ _

lemma dgGluingHomTargetUnitCapIntervalTriangle_first_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 0 =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 1 := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact dgGluingHomTargetUnitCapPastingTriangleFamily_first_diagonal R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_last_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 2 =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 3 := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact dgGluingHomTargetUnitCapPastingTriangleFamily_last_diagonal R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_first_bridge :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 1 =
      (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 5 := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact dgGluingHomTargetUnitCapPastingTriangleFamily_first_bridge R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_last_bridge :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 3 =
      (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 5 := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact dgGluingHomTargetUnitCapPastingTriangleFamily_last_bridge R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_coefficient_first :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 1 =
      (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 4 := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_first R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_coefficient_last :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 3 =
      (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 4 := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y]
  exact dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_last R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_collar_bridge :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 5 =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCollarIntervalTriangle R C D E p q X Y := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCollarIntervalTriangle_evaluate R C D E p q X Y]
  exact dgGluingHomTargetUnitCapPastingTriangleFamily_collar_bridge R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_first_cap :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 0 =
      (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
        dgGluingHomTargetPreCapInputPath R C D E p q X Y ≫
          dgGluingHomTargetFirstInputDiagonal R C D E p q X Y := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, dgGluingHomTargetUnitCapIntervalTriangle_evaluate,
    intervalMappingUncurry_precomp]
  exact dgGluingHomTargetUnitCapPastingTriangleFamily_first_cap R C D E p q X Y

lemma dgGluingHomTargetUnitCapIntervalTriangle_last_cap :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 2 =
      (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
        dgGluingHomTargetExitCapInputPath R C D E p q X Y ≫
          dgGluingHomTargetLastInputDiagonal R C D E p q X Y := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, dgGluingHomTargetUnitCapIntervalTriangle_evaluate,
    intervalMappingUncurry_precomp]
  exact dgGluingHomTargetUnitCapPastingTriangleFamily_last_cap R C D E p q X Y
end SerrePositivity.InfinityCategories
