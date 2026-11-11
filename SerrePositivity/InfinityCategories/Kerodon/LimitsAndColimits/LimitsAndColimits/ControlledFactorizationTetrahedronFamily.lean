module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FactorizationTetrahedronFaces
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronFamilyVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronStrictCompositionHom

/-!
概要：指定 T と二つの厳密合成面を保ち、欠面の全 native Hom を回収する三単体族。
方針：まず同じ三面を充填し、全頂点で長い Hom を正規化して同じ全ホーンへ延長する。
規約：全パラメーターと指定三面を厳密に保持し、全 native Hom の HEq を供給する。
使われ方：Ind-S (9b)、K-B の因子分解三単体族。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 指定三面と、指定 T の全 native Hom を保持する因子分解三単体族。 -/
lemma controlledFactorizationTetraFamily
    (X₀ X₁ X₂ X₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (K : SSet.{u + 1}) (T : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (f ≫ g)).edge)
    (hlast : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h).edge) :
    ∃ F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct g h).simplex ∧
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ F = T ∧
      (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex ∧
      ∀ k : K _⦋0⦌,
        let t := SSet.yonedaEquiv (lift (𝟙 (Δ[3] : SSet.{u + 1})) (SSet.const k) ≫ F)
        let a := SSet.yonedaEquiv (lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const k) ≫ T)
        HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 4) t).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
          (a.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  classical
  obtain ⟨F₀, h₀, h₁, h₃⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.factorizationTetrahedronFamily_faces X₀ X₁ X₂ X₃ f g h K T
    hfirst hlast
  let t (k : K _⦋0⦌) := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F₀ k)
  have face (k : K _⦋0⦌) (i : Fin 4) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌)
      (ha : (stdSimplex.δ i ▷ K) ≫ F₀ =
        fst (Δ[2] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm a) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ i (t k) = a := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, ha,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_constant, Equiv.apply_symm_apply]
  have normalize (k : K _⦋0⦌) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedron_normalize_of_strict_faces (t k)
    ((⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin 3) →o Fin 3).toFunctor ⋙
      ComposableArrows.mk₂ g h)
    ((⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin 3) →o Fin 3).toFunctor ⋙
      ComposableArrows.mk₂ f g)
    (face k 0 _ h₀) (face k 3 _ h₃)
  choose tn hn₀ hn₁ hn₃ hnHom using normalize
  obtain ⟨F, hF, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerHornFamily_exists_with_vertex_fillers 3 2 (by decide) (by decide) K F₀
    (fun k => SSet.yonedaEquiv.symm (tn k)) (by
      intro k
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedron_horn_eq_of_faces
      all_goals
        apply SSet.yonedaEquiv.injective
        rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
          Equiv.apply_symm_apply]
      · exact hn₀ k
      · exact hn₁ k
      · exact hn₃ k)
  refine ⟨F, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerHornFamily_face_of_restriction 2 F F₀ hF 0 (by decide)).trans h₀,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerHornFamily_face_of_restriction 2 F F₀ hF 1 (by decide)).trans h₁,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerHornFamily_face_of_restriction 2 F F₀ hF 3 (by decide)).trans h₃, ?_⟩
  intro k
  change HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 4) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k))).map
      ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
    ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex T k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
  rw [hv, Equiv.apply_symm_apply]
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (1 : Fin 4) (t k) = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex T k) := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, h₁]
  exact (hnHom k).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctor_map_heq ht _ _)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
