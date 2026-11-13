module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedQuasiIsomorphisms
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OrdinaryNatTransPrism

import all Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：元の通常の複体値自然変換を全nerveの円柱とし、成分が擬同型なら全関手同型にする。
方針：二つの図式の実際の変換から有限順序の評価を作り、同じ成分の反転を使う。
規約：対象宇宙u+1と射宇宙uを保つ。点ごとの同型を自然なものと仮定しない。
使われ方：3b-3 R6、元の単体的置換の増大の全パラメーター比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] {C : Type (u + 1)} [Category.{u} C]
  {F G : C ⥤ Complex A} (η : F ⟶ G)

/-- 元の自然変換を有限順序と全射列で評価した、同じ通常nerveの円柱。 -/
def complexNatTransCylinder : (Δ[1] : SSet.{u + 1}) ⊗ nerve C ⟶ nerve (Complex A) :=
  ordinaryNatTransPrism η

/-- 同じ円柱の両端は、元の二つの通常図式のnerveである。 -/
lemma complexNatTransCylinder_endpoint (i : Fin 2) :
    prismEndpoint i (nerve C) ≫ complexNatTransCylinder A η =
      nerveMap ((ComposableArrows.mk₁ η).obj i) := by
  fin_cases i
  · exact ordinaryNatTransPrism_zero η
  · exact ordinaryNatTransPrism_one η

/-- 固定対象の垂直辺は、元の自然変換の同じ成分である。 -/
lemma complexNatTransCylinder_vertical (X : C) :
    (complexNatTransCylinder A η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})),
        PinchedHom.constant (ComposableArrows.mk₀ X) 1) =
      ComposableArrows.mk₁ (η.app X) := by
  exact ordinaryNatTransPrism_vertexEdge η X

set_option maxHeartbeats 800000 in
/-- 同じ成分が全て擬同型である通常自然変換から、全パラメーターの関手同型を得る。 -/
def complexDerivedNatTransIso (hη : ∀ X, QuasiIso (η.app X)) :
    FunctorIso (nerveMap F ≫ complexDerivedEvaluation A)
      (nerveMap G ≫ complexDerivedEvaluation A) := by
  let H := complexNatTransCylinder A η ≫ complexDerivedEvaluation A
  have hv : ∀ x : (nerve C) _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})), PinchedHom.constant x 1))) := by
    intro x
    obtain ⟨X, rfl⟩ := nerveEquiv.symm.surjective x
    have : QuasiIso (η.app X) := hη X
    have hi := complexDerivedEvaluation_inverts_quasiIso A (η.app X)
    apply (isInvertibleEdge_congr (f := edgeOfSimplex
      ((complexDerivedEvaluation A).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ (η.app X)))) ?_).mpr hi
    exact congrArg (fun s => (complexDerivedEvaluation A).app (Opposite.op ⦋1⦌) s)
      (complexNatTransCylinder_vertical A η X)
  have h := @functorIsoOfEquivalenceHomotopy.{u + 1} (nerve C)
    (derivedInfinityCategory A) (derivedInfinityCategoryQuasicategory A) H hv
  simpa only [H, ← Category.assoc, complexNatTransCylinder_endpoint] using! h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
