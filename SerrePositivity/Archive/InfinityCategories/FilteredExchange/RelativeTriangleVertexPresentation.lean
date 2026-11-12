module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UnstraighteningTriangleRelativeVertex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：指定 coherent 三角形の全空間作用を底を固定した相対写像空間内で比較する。
方針：全族の三角形比較を零単体で評価し、相対頂点の厳密な合成式を使う。
規約：三辺と三角形を変更しない。使われ方：標的の単位との合成の指定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {B : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
    (z : (leftUnstraighteningTransformationSpace F J) _⦋0⦌)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const x))
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const y))
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const z))

local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "e" => unstraighteningTriangleRelativeVertexIso F G J x y z H h₀₁ h₁₂ h₀₂
local notation "e₀" => FunctorIso.app (unstraighteningMappingTriangleIso F G J
  (SSet.const x) (SSet.const y) (SSet.const z) H h₀₁ h₁₂ h₀₂) l

/-- 元の相対頂点の指定比較は、同じ実際の三角形比較の成分の端点正規化。 -/
lemma unstraighteningTriangleRelativeVertexIso_heq_component : HEq e e₀ := by
  unfold unstraighteningTriangleRelativeVertexIso
  dsimp only
  exact iso_endpoints_heq _ _ _

/-- 端点の頂点表示を変えても同じ始域制限の指定比較になる。 -/
lemma unstraighteningTriangleRelativeVertexIso_map_pre_heq_component
    {C : SSet.{u + 1}} (s : C ⟶ leftUnstraightening F) :
    HEq (VertexIso.map e
      (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) s))
      (VertexIso.map e₀
        (relativeFunctorPre (leftUnstraighteningProjection J)
          (leftUnstraighteningProjection F) s)) := by
  exact vertexIso_map_heq_of_heq e e₀
    (unstraighteningMappingConst_vertex F J z l).symm
    (unstraighteningMappingConstComposite_vertex F G J x y l).symm
    (unstraighteningTriangleRelativeVertexIso_heq_component F G J x y z H h₀₁ h₁₂ h₀₂)
    (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) s)

end SerrePositivity.InfinityCategories.F2
