module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningTrianglePrismWitness

/-!
概要：元の写像空間作用の二辺に沿う全 pointed 三角形を公開する。
方針：普遍的な持ち上げを二つの指定族へ制限し、元の全三角形上で充填する。
規約：全パラメータを保持。使われ方：指定比較同型と元の二単体の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定族の写像空間作用を表す元の普遍的な pointed 証拠。
方針：普遍証拠を元の族で制限する。
規約：作用射の定義と同じ証拠。使われ方：全三角形の二辺を固定する。 -/
def unstraighteningMappingFamilyWitness {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (a : K ⟶ leftUnstraighteningTransformationSpace F G) :
    UnstraighteningFamilyWitness F G a
      (relativeFunctorUncurry (a ≫ leftUnstraighteningMappingSpaceMap F G)) where
  prism := ((Δ[1] ⊗ leftUnstraightening F) ◁ a) ≫
    leftUnstraighteningTransformationFamilyLift F G
  source := ((unstraighteningUniversalFamilyWitness F G).comp a).source
  target := by
    simpa only [UnstraighteningFamilyWitness.comp, unstraighteningUniversalFamilyWitness,
      relativeFunctorUncurry_naturality] using
      ((unstraighteningUniversalFamilyWitness F G).comp a).target
  projection := by
    simpa only [UnstraighteningFamilyWitness.comp, unstraighteningUniversalFamilyWitness,
      Category.comp_id] using
      ((unstraighteningUniversalFamilyWitness F G).comp a).projection

/-- 概要：元の写像空間作用の二辺を保つ元の底の全三角形の持ち上げ。
方針：指定された二つの普遍証拠を元の二単体上で充填する。
規約：元の二単体が返り値の型に残る。使われ方：指定三角形比較の証拠。 -/
def unstraighteningMappingTrianglePrism {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (a : K ⟶ leftUnstraighteningTransformationSpace F G)
    (b : K ⟶ leftUnstraighteningTransformationSpace G J)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram a)
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram b) :
    TransportTrianglePrism (unstraighteningMappingFamilyWitness F G a).toRepresentationWitness
      (unstraighteningMappingFamilyWitness G J b).toRepresentationWitness H :=
  transportTrianglePrism
    (relativeFunctorUncurry_projection (a ≫ leftUnstraighteningMappingSpaceMap F G))
    (unstraighteningMappingFamilyWitness F G a).toRepresentationWitness
    (unstraighteningMappingFamilyWitness G J b).toRepresentationWitness H h₀₁ h₁₂

/-- 概要：元の二単体の持ち上げの長辺による指定合成証拠。
方針：保持した全 prism の長辺を直接制限。
規約：証拠を再選択しない。使われ方：指定比較同型の入力。 -/
def unstraighteningMappingTriangleLongWitness {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (a : K ⟶ leftUnstraighteningTransformationSpace F G)
    (b : K ⟶ leftUnstraighteningTransformationSpace G J)
    (c : K ⟶ leftUnstraighteningTransformationSpace F J)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram a)
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram b)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram c) :=
  unstraighteningFamilyTriangleWitnessOfPrism F G J
    (unstraighteningMappingFamilyWitness F G a) (unstraighteningMappingFamilyWitness G J b) H
    (unstraighteningMappingTrianglePrism F G J a b H h₀₁ h₁₂) h₀₂

end SerrePositivity.InfinityCategories.F2
