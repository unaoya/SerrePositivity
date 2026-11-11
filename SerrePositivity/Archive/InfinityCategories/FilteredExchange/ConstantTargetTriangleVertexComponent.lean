module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeTriangleVertexPresentation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningRelativeProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentPost
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UnstraighteningTriangleVertex

/-!
概要：定値標的の元の全空間三角形比較の fiber 像を、同じ全族比較の一点成分へ戻す。
方針：相対頂点比較の表示変更と全相対 Hom 上の fiber 射影の公式を使う。
規約：三辺・全二単体・指定比較を保持。使われ方：元の長辺輸送との値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全空間三角形比較の fiber 像は、同じ全族の相対比較の fiber 像の一点成分。 -/
lemma constantTargetTriangleVertexIso_heq_component {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (z : SpaceInfinity.{u} _⦋0⦌)
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (leftUnstraighteningTransformationSpace G (SSet.const z)) _⦋0⦌)
    (c : (leftUnstraighteningTransformationSpace F (SSet.const z)) _⦋0⦌)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const x))
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const y))
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const c)) :
    HEq ((unstraighteningTriangleVertexIso F G (SSet.const z) x y c H h₀₁ h₁₂ h₀₂).postcomp
      (constantUnstraighteningFiberProjection B z))
      (((unstraighteningMappingTriangleIso F G (SSet.const z)
        (SSet.const x) (SSet.const y) (SSet.const c) H h₀₁ h₁₂ h₀₂).postcomp
          (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom).app
            (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) := by
  let l : (Δ[0] : SSet.{u + 1}) _⦋0⦌ := stdSimplex.obj₀Equiv.symm 0
  let e := unstraighteningTriangleRelativeVertexIso F G (SSet.const z) x y c H h₀₁ h₁₂ h₀₂
  let e₀ := unstraighteningMappingTriangleIso F G (SSet.const z)
    (SSet.const x) (SSet.const y) (SSet.const c) H h₀₁ h₁₂ h₀₂
  rw [functorIso_postcomp_eq_mapIso]
  unfold unstraighteningTriangleVertexIso
  change HEq (VertexIso.map (VertexIso.map e
    (vertexFiberι ((ihom (leftUnstraightening F)).map
      (leftUnstraighteningProjection (SSet.const z)))
      (functorVertex (leftUnstraighteningProjection F))))
    ((ihom (leftUnstraightening F)).map (constantUnstraighteningFiberProjection B z))) _
  refine (heq_of_eq (vertexIso_map_comp e _ _)).trans ?_
  refine (vertexIso_map_heq e
    (constantUnstraighteningRelativeIso_hom_eq_projection
      (leftUnstraighteningProjection F) z).symm).trans ?_
  have he := vertexIso_map_heq_of_heq e (e₀.app l)
    (unstraighteningMappingConst_vertex F (SSet.const z) c l).symm
    (unstraighteningMappingConstComposite_vertex F G (SSet.const z) x y l).symm
    (unstraighteningTriangleRelativeVertexIso_heq_component F G (SSet.const z)
      x y c H h₀₁ h₁₂ h₀₂)
    (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom
  exact he.trans (functorIso_app_postcomp_heq e₀ _ l).symm

end SerrePositivity.InfinityCategories.F2
