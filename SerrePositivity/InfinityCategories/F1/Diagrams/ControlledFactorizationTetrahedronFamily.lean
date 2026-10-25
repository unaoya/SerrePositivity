module

public import SerrePositivity.InfinityCategories.F1.Diagrams.FactorizationTetrahedronFaces
public import SerrePositivity.InfinityCategories.F1.Diagrams.TetrahedronFamilyVertices
public import SerrePositivity.InfinityCategories.F1.Diagrams.TetrahedronStrictCompositionHom

/-!
概要：指定 T と二つの厳密合成面を保ち、欠面の全 native Hom を回収する三単体族。
方針：まず同じ三面を充填し、全頂点で長い Hom を正規化して同じ全ホーンへ延長する。
規約：全パラメーターと指定三面を厳密に保持し、全 native Hom の HEq を供給する。
使われ方：Ind-S (9b)、K-B の因子分解三単体族。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定三面と、指定 T の全 native Hom を保持する因子分解三単体族。 -/
lemma controlledFactorizationTetraFamily
    (X₀ X₁ X₂ X₃ : KanObject.{u})
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (K : SSet.{u + 1}) (T : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u})
    (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (coherentNerveEdge (f ≫ g)).edge)
    (hlast : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (coherentNerveEdge h).edge) :
    ∃ F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u},
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (coherentNerveCompStruct g h).simplex ∧
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ F = T ∧
      (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (coherentNerveCompStruct f g).simplex ∧
      ∀ k : K _⦋0⦌,
        let t := SSet.yonedaEquiv (lift (𝟙 (Δ[3] : SSet.{u + 1})) (SSet.const k) ≫ F)
        let a := SSet.yonedaEquiv (lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const k) ≫ T)
        HEq ((SpaceInfinity.δ (2 : Fin 4) t).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
          (a.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  classical
  obtain ⟨F₀, h₀, h₁, h₃⟩ := factorizationTetrahedronFamily_faces X₀ X₁ X₂ X₃ f g h K T
    hfirst hlast
  let t (k : K _⦋0⦌) := SSet.yonedaEquiv (familyAtVertex F₀ k)
  have face (k : K _⦋0⦌) (i : Fin 4) (a : SpaceInfinity.{u} _⦋2⦌)
      (ha : (stdSimplex.δ i ▷ K) ≫ F₀ =
        fst (Δ[2] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm a) :
      SpaceInfinity.δ i (t k) = a := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← familyAtVertex_precomp, ha,
      familyAtVertex_constant, Equiv.apply_symm_apply]
  have normalize (k : K _⦋0⦌) := tetrahedron_normalize_of_strict_faces (t k)
    ((⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin 3) →o Fin 3).toFunctor ⋙
      ComposableArrows.mk₂ g h)
    ((⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin 3) →o Fin 3).toFunctor ⋙
      ComposableArrows.mk₂ f g)
    (face k 0 _ h₀) (face k 3 _ h₃)
  choose tn hn₀ hn₁ hn₃ hnHom using normalize
  obtain ⟨F, hF, hv⟩ := innerHornFamily_exists_with_vertex_fillers 3 2 (by decide) (by decide) K F₀
    (fun k => SSet.yonedaEquiv.symm (tn k)) (by
      intro k
      apply tetrahedron_horn_eq_of_faces
      all_goals
        apply SSet.yonedaEquiv.injective
        rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
          Equiv.apply_symm_apply]
      · exact hn₀ k
      · exact hn₁ k
      · exact hn₃ k)
  refine ⟨F, (innerHornFamily_face_of_restriction 2 F F₀ hF 0 (by decide)).trans h₀,
    (innerHornFamily_face_of_restriction 2 F F₀ hF 1 (by decide)).trans h₁,
    (innerHornFamily_face_of_restriction 2 F F₀ hF 3 (by decide)).trans h₃, ?_⟩
  intro k
  change HEq ((SpaceInfinity.δ (2 : Fin 4) (SSet.yonedaEquiv (familyAtVertex F k))).map
      ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
    ((SSet.yonedaEquiv (familyAtVertex T k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
  rw [hv, Equiv.apply_symm_apply]
  have ht : SpaceInfinity.δ (1 : Fin 4) (t k) = SSet.yonedaEquiv (familyAtVertex T k) := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← familyAtVertex_precomp, h₁]
  exact (hnHom k).trans (enrichedFunctor_map_heq ht _ _)

end SerrePositivity.InfinityCategories
