module

public import SerrePositivity.InfinityCategories.F1.DiagonalCocartesianSectionsConstant
public import SerrePositivity.InfinityCategories.F1.CocartesianStraighteningCoherent
public import SerrePositivity.InfinityCategories.F1.CocartesianStrictTransportDiagram
public import SerrePositivity.InfinityCategories.F1.CocartesianFibrationMappingSpaces

/-!
概要：構成済みの同じ Cat∞ 値分類写像の、元の fibration の標準頂点での値を照合する。
方針：定値な coherent パラメーターの対角評価を、元の section の strict transport 図式へ戻す。
規約：各 fiber の値だけでなく、同じ分類図式全体の厳密な等式を証明する。
使われ方：Cat∞ 値 straightening の再構成比較と、写像空間の充満忠実性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ底の射列上の section の図式は、元の cocartesian strict transport の制限である。 -/
lemma strictTransportSimplex_cocartesianSectionsQCatDiagram
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    cocartesianSectionsQCatDiagram (strictTransportSimplexUnderDiagram σ)
      (cocartesianFibrationObjectOf p) =
      (⟨ULift.down, fun _ _ h ↦ h⟩ :
        ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙ σ ⋙
        cocartesianStrictTransportQCatFunctor p := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  rfl

/-- 同じ fibration の coherent パラメーターを固定すると、元の strict transport 図式を回収する。 -/
lemma cocartesianStrictTransportDiagonalSimplex_constant
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    cocartesianStrictTransportDiagonalSimplex σ
      (PinchedHom.constant (cocartesianFibrationInfinityVertex p) n) =
    (cocartesianStrictTransportCoherentDiagram p).app (Opposite.op ⦋n⦌) (ULift.up σ) := by
  change diagonalCocartesianSectionsEvaluation (strictTransportSimplexUnderDiagram σ)
    (PinchedHom.constant (coherentNerveVertex (cocartesianFibrationObjectOf p)) n) =
      enrichedFunctorOfOrderDiagram _
  rw [coherentNerveVertex_constant, diagonalCocartesianSectionsEvaluation_constant,
    strictTransportSimplex_cocartesianSectionsQCatDiagram]

/-- 構成済みの同じ分類写像は、元の cocartesian section の strict transport 図式そのものを分類する。 -/
lemma cocartesianStraighteningCoherentMap_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] :
    (cocartesianStraighteningCoherentMap C).app (Opposite.op ⦋0⦌)
      (cocartesianFibrationInfinityVertex p) =
      functorVertex (cocartesianStrictTransportCoherentDiagram p) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro σ
  exact cocartesianStrictTransportDiagonalSimplex_constant p σ.down

end SerrePositivity.InfinityCategories
