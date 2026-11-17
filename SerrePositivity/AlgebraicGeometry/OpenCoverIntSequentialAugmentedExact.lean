module

public import SerrePositivity.AlgebraicGeometry.CechIntSequentialAugmentedExact
public import SerrePositivity.AlgebraicGeometry.OpenCoverSequentialCech

/-!
概要：同じ被覆の整数係数の増大完全性を前層の自然数順極限に渡す。
方針：既存の交叉への制限と、各有限段の同じ完全性の移送を使う。
規約：増大項の単射性と全長さの完全性を直接返し、任意の宇宙の整数加群を扱う。
使われ方：アフィン被覆の実際の Frobenius 係数への代入。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type} [DecidableEq ι] [Fintype ι]

/-- 前層の同じ被覆における増大完全性は、整数係数の任意の宇宙で自然数順極限へ移る。 -/
theorem openCoverIntSequential_augmentedExact
    (P : ℕ ⥤ (Opens X)ᵒᵖ ⥤ ModuleCat.{v} ℤ) (U : ι → Opens X)
    (h : ∀ n, Function.Injective (fullCechDifferential (openCoverCechDiagram (P.obj n) U) 0) ∧
      ∀ k, Function.Exact (fullCechDifferential (openCoverCechDiagram (P.obj n) U) k)
        (fullCechDifferential (openCoverCechDiagram (P.obj n) U) (k + 1))) :
    Function.Injective (fullCechDifferential (openCoverCechDiagram (colimit P) U) 0) ∧
      ∀ k, Function.Exact (fullCechDifferential (openCoverCechDiagram (colimit P) U) k)
        (fullCechDifferential (openCoverCechDiagram (colimit P) U) (k + 1)) := by
  let W : ((Opens X)ᵒᵖ ⥤ ModuleCat.{v} ℤ) ⥤ Finset ι ⥤ ModuleCat.{v} ℤ :=
    (Functor.whiskeringLeft _ _ _).obj (openCoverCechIndexFunctor U)
  let D := P ⋙ W
  have hD := fullCechIntSequential_augmentedExact D h
  let e : openCoverCechDiagram (colimit P) U ≅ colimit D := preservesColimitIso W P
  exact ⟨fullCechCoefficientEquiv_zero_injective e.symm hD.1,
    fun k ↦ fullCechCoefficientEquiv_exact e.symm k (hD.2 k)⟩

end SerrePositivity.AlgebraicGeometry
