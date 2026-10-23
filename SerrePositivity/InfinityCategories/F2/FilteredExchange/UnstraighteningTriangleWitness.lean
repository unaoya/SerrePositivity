module

public import SerrePositivity.InfinityCategories.F1.TransportRepresentationCompositionFamily
public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyWitnessRestriction

/-!
概要：指定した coherent な三角形に沿う unstraightening の族の合成の証拠。
方針：F1 の一般表現の合成証拠を標準表現へ適用する。
規約：F1 の実装は変更せず、指定三角形と全パラメータを保持する。
使われ方：全 Hom の余錐の合成と全空間比較の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二つの pointed な変換の証拠を指定三角形の長辺の合成証拠へ貼り合わせる。
方針：標準表現へ移し、既存の三角柱の充填から証拠を取り戻す。
規約：底・高次パラメータは任意。使われ方：実際の比較射の合成則。 -/
lemma unstraighteningFamilyTriangleWitness {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    {a : K ⟶ leftUnstraighteningTransformationSpace F G}
    {b : K ⟶ leftUnstraighteningTransformationSpace G J}
    {c : K ⟶ leftUnstraighteningTransformationSpace F J}
    {f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G}
    {g : leftUnstraightening G ⊗ K ⟶ leftUnstraightening J}
    (hf : f ≫ leftUnstraighteningProjection G =
      fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
    (w : UnstraighteningFamilyWitness F G a f)
    (v : UnstraighteningFamilyWitness G J b g)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram a)
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram b)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram c) :
    Nonempty (UnstraighteningFamilyWitness F J c (lift f (snd (leftUnstraightening F) K) ≫ g)) := by
  obtain ⟨W⟩ := transportRepresentationCompositionFamilyWitness_nonempty
    (unstraighteningTransportRepresentation F) (unstraighteningTransportRepresentation G)
    (unstraighteningTransportRepresentation J) hf w.toRepresentationWitness
    v.toRepresentationWitness H h₀₁ h₁₂ h₀₂
  refine ⟨⟨W.prism, ?_, ?_, W.projection⟩⟩
  · simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using W.source
  · simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using W.target

end SerrePositivity.InfinityCategories.F2
