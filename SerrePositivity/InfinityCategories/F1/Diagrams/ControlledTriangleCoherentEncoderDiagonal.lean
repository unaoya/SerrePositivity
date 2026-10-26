module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleCoherentEncoder
public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleUniversalVertices

/-!
概要：実 encode の各入力で、元の長 Hom 全族の直接 path 評価を全長辺として厳密回収する。
方針：普遍族の同じ L 頂点への制限と、実証済みの全対角式を接続する。
規約：K の全族の射の等式。厳密切断 encode ≫ read = id は別途。
使われ方：採用済み normalize(t) に対する全対角条項と固定ホーン内の可逆比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
  (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
  (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u})
  (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
    (Δ[1] ◁ f) ≫ intervalMappingUncurry (coherentHomIntervalComparison X Y))
  (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
    (Δ[1] ◁ g) ≫ intervalMappingUncurry (coherentHomIntervalComparison Y Z))

lemma controlledTriangleCoherentEncoder_value
    (l : (controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)) _⦋0⦌) :
    controlledTriangleFamilyValue
        ((controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋0⦌) l) =
      (Δ[2] ◁ lift (𝟙 K) (SSet.const l)) ≫ controlledTriangleCoherentFamily X Y Z K f g := by
  change (functorVertexEquiv _ _).symm
    ((curry ((α_ (Δ[2] : SSet.{u + 1}) K _).hom ≫
      controlledTriangleCoherentFamily X Y Z K f g)).app (Opposite.op ⦋0⦌) l) = _
  rw [curry_app_vertex]
  calc
    _ = familyAtVertex ((α_ (Δ[2] : SSet.{u + 1}) K _).hom ≫
        controlledTriangleCoherentFamily X Y Z K f g) l :=
      (functorVertexEquiv _ _).symm_apply_apply _
    _ = _ := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      rfl

/-- 同じ l の元の全長 Hom を直接 path {0,2} で評価した標準全長辺。 -/
lemma controlledTriangleCoherentEncoder_diagonal
    (l : (controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)) _⦋0⦌) :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ controlledTriangleFamilyValue
        ((controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋0⦌) l) =
      (Δ[1] ◁ (controlledTriangleLongHomValue l ≫ evaluateFunctorAt
        (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
        (ULift.up (ComposableArrows.mk₀ triangleDirectPath.{u})))) ≫
        intervalMappingUncurry (coherentHomIntervalComparison X Z) := by
  rw [controlledTriangleCoherentEncoder_value]
  let P := lift (𝟙 K) (SSet.const l)
  calc
    _ = (Δ[1] ◁ P) ≫ (stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        controlledTriangleCoherentFamily X Y Z K f g := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro w
      rfl
    _ = (Δ[1] ◁ P) ≫ (Δ[1] ◁ (prismEndpoint 0 _ ≫
        uncurry (controlledTriangleUniversalInterval X Z K
          (controlledTriangleCompositeFamily X Y Z K f g)))) ≫
          intervalMappingUncurry (coherentHomIntervalComparison X Z) :=
      congrArg (fun h => (Δ[1] ◁ P) ≫ h)
        (controlledTriangleCoherentFamily_diagonal X Y Z K f g)
    _ = _ := by
      rw [← whiskerLeft_comp_assoc,
        controlledTriangleUniversalInterval_direct_at_vertex X Z K _ l]

/-- 同じ実 read を用いた normalize(t) の全対角は、読み出した全長 Hom の直接評価。 -/
lemma controlledTriangleCoherentNormalization_diagonal
    (read : controlledTriangleFamilySpace K a ⟶ controlledTriangleLongHomSpace X Z K
      (controlledTriangleCompositeFamily X Y Z K f g))
    (t : (controlledTriangleFamilySpace K a) _⦋0⦌) :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ controlledTriangleFamilyValue
        ((read ≫ controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋0⦌) t) =
      (Δ[1] ◁ (controlledTriangleLongHomValue (read.app (Opposite.op ⦋0⦌) t) ≫ evaluateFunctorAt
        (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
        (ULift.up (ComposableArrows.mk₀ triangleDirectPath.{u})))) ≫
        intervalMappingUncurry (coherentHomIntervalComparison X Z) :=
  controlledTriangleCoherentEncoder_diagonal X Y Z K f g a hf hg (read.app (Opposite.op ⦋0⦌) t)

/-- 元の t と同じ元の全ホーン fiber 内で比較する実 VertexIso。 -/
lemma controlledTriangleCoherentNormalization_vertexIso
    (read : controlledTriangleFamilySpace K a ⟶ controlledTriangleLongHomSpace X Z K
      (controlledTriangleCompositeFamily X Y Z K f g))
    (t : (controlledTriangleFamilySpace K a) _⦋0⦌) :
    Nonempty (VertexIso t
      ((read ≫ controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋0⦌) t)) :=
  controlledTriangleFamilyMaps_vertexIso X Z K _ a
    (controlledTriangleCoherentEncoder X Y Z K f g a hf hg) read t

end SerrePositivity.InfinityCategories
