module

public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationCompositionFamily

/-!
概要：選択した straightening の写像空間比較の合成則。
方針：普遍的な比較の証拠の二辺を三角形へ延長し長辺を族の一意性で比較する。
規約：比較する射は実際の相対関手空間の豊穣合成。
使われ方：一般の left fibrations 全体の coherent な分類の関手性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：選択した比較の二辺を持つ任意の指定三角形の長辺は合成の像と関手同型。
方針：指定三角形を pointed に持ち上げ、実際の豊穣合成の普遍族と比較する。
規約：三角形を選び直さず、後続の境界固定の高次比較に使える形にする。
使われ方：三重以上の合成を同じ高次単体の面に沿って比較する。 -/
lemma transportRepresentationMappingSpaceMap_compositionFamily_of_triangle
    {E F G B K : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ B} {r : G ⟶ B}
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (hp : HasSmallSimplexFibers p) (hq : HasSmallSimplexFibers q)
    (hr : HasSmallSimplexFibers r)
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation q)
    (T : LeftTransportRepresentation r)
    (a : K ⟶ relativeFunctorSpace q p) (b : K ⟶ relativeFunctorSpace r q)
    (t : K ⟶ leftUnstraighteningTransformationSpace R.diagram T.diagram)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram
        (a ≫ transportRepresentationMappingSpaceMap hp hq R S))
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram
        (b ≫ transportRepresentationMappingSpaceMap hq hr S T))
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram t) :
    Nonempty (FunctorIso
      ((lift a b ≫ relativeFunctorComposition (Over.mk p) (Over.mk q) (Over.mk r)) ≫
        transportRepresentationMappingSpaceMap hp hr R T) t) := by
  obtain ⟨w⟩ := transportRepresentationCompositionFamilyWitness_nonempty R S T
    (relativeFunctorUncurry_projection a)
    (transportRepresentationMappingFamilyWitness hp hq R S a)
    (transportRepresentationMappingFamilyWitness hq hr S T b) H h₀₁ h₁₂ h₀₂
  let c := lift a b ≫ relativeFunctorComposition (Over.mk p) (Over.mk q) (Over.mk r)
  have hc : relativeFunctorUncurry c =
      lift (relativeFunctorUncurry a) (snd E K) ≫ relativeFunctorUncurry b := by
    apply SSet.hom_ext
    intro n
    rfl
  have w' : TransportRepresentationFamilyWitness R T t (relativeFunctorUncurry c) := by
    rw [hc]
    exact w
  exact transportRepresentationMappingFamily_comparison hp hr R T c w'

/-- 概要：選択分類の二つの射の族の像は合成の像を長辺と同型に持つ三角形へ延長する。
方針：pointed な三角形の長辺と普遍的な比較の証拠を同じ相対射の族として比較する。
規約：点ごとの合成に落とさず、任意の高次パラメーターで構成する。
使われ方：写像空間上の作用の合成則。 -/
lemma transportRepresentationMappingSpaceMap_compositionFamily
    {E F G B K : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ B} {r : G ⟶ B}
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (hp : HasSmallSimplexFibers p) (hq : HasSmallSimplexFibers q)
    (hr : HasSmallSimplexFibers r)
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation q)
    (T : LeftTransportRepresentation r)
    (a : K ⟶ relativeFunctorSpace q p) (b : K ⟶ relativeFunctorSpace r q) :
    ∃ (t : K ⟶ leftUnstraighteningTransformationSpace R.diagram T.diagram)
      (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u}),
      (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        coherentTransformationFamilyDiagram
          (a ≫ transportRepresentationMappingSpaceMap hp hq R S) ∧
      (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        coherentTransformationFamilyDiagram
          (b ≫ transportRepresentationMappingSpaceMap hq hr S T) ∧
      (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        coherentTransformationFamilyDiagram t ∧
      Nonempty (FunctorIso
        ((lift a b ≫ relativeFunctorComposition (Over.mk p) (Over.mk q) (Over.mk r)) ≫
          transportRepresentationMappingSpaceMap hp hr R T) t) := by
  obtain ⟨t, H, h₀₁, h₁₂, h₀₂⟩ := coherentTransformationFamilyTriangle_nonempty
    (a ≫ transportRepresentationMappingSpaceMap hp hq R S)
    (b ≫ transportRepresentationMappingSpaceMap hq hr S T)
  exact ⟨t, H, h₀₁, h₁₂, h₀₂,
    transportRepresentationMappingSpaceMap_compositionFamily_of_triangle
      hp hq hr R S T a b t H h₀₁ h₁₂ h₀₂⟩

/-- 概要：小さい次数 fiber の選択分類の合成則は全高次パラメーターで成立する。
方針：一般の表現の合成則を選択した分類へ適用する。
規約：底の quasicategory 性は必要ない。
使われ方：選択 straightening の coherent な関手性の二単体の入力。 -/
lemma smallFiberLeftStraighteningMappingSpaceMap_compositionFamily
    {E F G B K : SSet.{u + 1}}
    (p : E ⟶ B) (q : F ⟶ B) (r : G ⟶ B)
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (hp : HasSmallSimplexFibers p) (hq : HasSmallSimplexFibers q)
    (hr : HasSmallSimplexFibers r)
    (a : K ⟶ relativeFunctorSpace q p) (b : K ⟶ relativeFunctorSpace r q) :
    ∃ (t : K ⟶ leftUnstraighteningTransformationSpace
        (smallFiberLeftStraighteningDiagram p hp) (smallFiberLeftStraighteningDiagram r hr))
      (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u}),
      (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        coherentTransformationFamilyDiagram
          (a ≫ smallFiberLeftStraighteningMappingSpaceMap p q hp hq) ∧
      (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        coherentTransformationFamilyDiagram
          (b ≫ smallFiberLeftStraighteningMappingSpaceMap q r hq hr) ∧
      (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        coherentTransformationFamilyDiagram t ∧
      Nonempty (FunctorIso
        ((lift a b ≫ relativeFunctorComposition (Over.mk p) (Over.mk q) (Over.mk r)) ≫
          smallFiberLeftStraighteningMappingSpaceMap p r hp hr) t) :=
  transportRepresentationMappingSpaceMap_compositionFamily hp hq hr
    (smallFiberLeftStraighteningRepresentation p hp)
    (smallFiberLeftStraighteningRepresentation q hq)
    (smallFiberLeftStraighteningRepresentation r hr) a b

end SerrePositivity.InfinityCategories
