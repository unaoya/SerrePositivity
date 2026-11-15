module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeOverDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：元の大域二重 cone を、恒等錐から同じ slice 図式への全区間 prism に移す。
方針：同じ join 円柱比較を使い、両端を元の先端と通常図式へ厳密に回収する。
規約：HA Construction 1.3.1.6・1.3.1.13、元の全区間族を保持する。使われ方：同じ augmentation・評価との大域三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorDoubleConeSlicePrism : (Δ[1] : SSet.{u + 1}) ⊗
    nerve (strictRawModuleTensorElementIndex A X P Q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P) :=
  (lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 (Δ[1] : SSet.{u + 1})) ▷
      nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorDoubleConeOverJoin A X P Q

lemma strictRawModuleTensorDoubleConeSlicePrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorDoubleConeSlicePrism A X P Q =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))) := by
  let K := nerve (strictRawModuleTensorElementIndex A X P Q)
  let s : K ⟶ (Δ[0] : SSet.{u + 1}) ⊗ K :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 K)
  let d : (Δ[1] : SSet.{u + 1}) ⟶ (Δ[0] : SSet.{u + 1}) ⊗ Δ[1] :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 Δ[1])
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (d ▷ K) = s ≫ (SSet.ι₀ (X := Δ[0]) ▷ K) := by rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ ((d ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] K ≫
    strictRawModuleTensorDoubleConeOverJoin A X P Q) = _
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (SSet.ι₀ (X := Δ[0]) ▷ K),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero, Category.assoc, strictRawModuleTensorDoubleConeOverJoin_inl]
  rw [← Category.assoc]
  have hs : s ≫ fst Δ[0] K =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := lift_fst _ _
  rw [hs, SSet.const_comp, strictRawModuleTensorIdentityOverPoint_vertex]

lemma strictRawModuleTensorDoubleConeSlicePrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorDoubleConeSlicePrism A X P Q = strictRawModuleTensorDoubleConeOverDiagram A X P Q := by
  let K := nerve (strictRawModuleTensorElementIndex A X P Q)
  let s : K ⟶ (Δ[0] : SSet.{u + 1}) ⊗ K :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 K)
  let d : (Δ[1] : SSet.{u + 1}) ⟶ (Δ[0] : SSet.{u + 1}) ⊗ Δ[1] :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 Δ[1])
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (d ▷ K) = s ≫ (SSet.ι₁ (X := Δ[0]) ▷ K) := by rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ ((d ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] K ≫
    strictRawModuleTensorDoubleConeOverJoin A X P Q) = _
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (SSet.ι₁ (X := Δ[0]) ▷ K),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one, Category.assoc, strictRawModuleTensorDoubleConeOverJoin_inr]
  rw [← Category.assoc]
  have hs : s ≫ snd Δ[0] K = 𝟙 K := lift_snd _ _
  rw [hs, Category.id_comp]

end SerrePositivity.EInfinity.BarrattEccles
