module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRefinedThreeApex
public import SerrePositivity.InfinityCategories.Derived.FullSubcomplexSimplexApexLift

/-! # 細分された図式二単体を実分母 over 三単体へ戻す

概要：追加閉分母後の同じ実四単体から、元の図式二単体を保つ実分母 over 三単体を構成。
方針：新 apex の合成分母性と元の零面の所属を任意次元の全部分複体持ち上げへ渡す。
規約：回収した台を変更しない。使われ方：有限二次図式の実高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))

variable [Small.{u} D] [IsDGPretriangulated A D]
variable (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  ((HornData.knownData (dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
variable (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
variable (F : Δ[4] ⟶ dgNerve A D)

/-- 元の二単体と同じ零面を持つ、閉細分後の実分母部分圏内の実三単体。 -/
def dgVerdierDiagramRefinedThreeSimplex
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (dgVerdierOver A D P x : SSet.{max u v}) _⦋3⦌ :=
  fullSubcomplexSimplexApexLift (IsDGVerdierOverVertex A D P x)
    (dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF) (f.app _ σ)
    (dgVerdierDiagramRefinedOverThreeSimplex_face0 A D C σ H q s F hF) (by
      have he : SimplexCategory.const ⦋0⦌ ⦋3⦌ 0 =
          (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3)) ≫
            SimplexCategory.δ (1 : Fin 4) :=
        SimplexCategory.Hom.ext_zero_left _ _ rfl
      rw [he, op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply]
      exact dgVerdierDiagramRefinedThreeApex_mem A D C σ H q s F hs hF)

/-- 実分母部分圏へ戻した三単体は、同じ四単体から回収した over 三単体のまま。 -/
lemma dgVerdierDiagramRefinedThreeSimplex_val
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (dgVerdierDiagramRefinedThreeSimplex A D C σ H q s hs F hF).val =
      dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF := rfl

/-- 持ち上げた実分母三単体の零面は、元の指定図式二単体そのもの。 -/
lemma dgVerdierDiagramRefinedThreeSimplex_face0
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (dgVerdierOver A D P x : SSet).δ 0
      (dgVerdierDiagramRefinedThreeSimplex A D C σ H q s hs F hF) = f.app _ σ :=
  Subtype.ext (dgVerdierDiagramRefinedOverThreeSimplex_face0 A D C σ H q s F hF)

end SerrePositivity.InfinityCategories
