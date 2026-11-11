module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierRefinedThreeApex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullSubcomplexSimplexApexLift

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
variable (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
variable (F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 元の二単体と同じ零面を持つ、閉細分後の実分母部分圏内の実三単体。 -/
def dgVerdierDiagramRefinedThreeSimplex
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋3⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullSubcomplexSimplexApexLift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF) (f.app _ σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex_face0 A D C σ H q s F hF) (by
      have he : SimplexCategory.const ⦋0⦌ ⦋3⦌ 0 =
          (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3)) ≫
            SimplexCategory.δ (1 : Fin 4) :=
        SimplexCategory.Hom.ext_zero_left _ _ rfl
      rw [he, op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedThreeApex_mem A D C σ H q s F hs hF)

/-- 実分母部分圏へ戻した三単体は、同じ四単体から回収した over 三単体のまま。 -/
lemma dgVerdierDiagramRefinedThreeSimplex_val
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (dgVerdierDiagramRefinedThreeSimplex A D C σ H q s hs F hF).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF := rfl

/-- 持ち上げた実分母三単体の零面は、元の指定図式二単体そのもの。 -/
lemma dgVerdierDiagramRefinedThreeSimplex_face0
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0
      (dgVerdierDiagramRefinedThreeSimplex A D C σ H q s hs F hF) = f.app _ σ :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex_face0 A D C σ H q s F hF)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
