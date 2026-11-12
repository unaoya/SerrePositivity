module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ContractibleIsoComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：始点固定の全三単体の延長を、同じ始点を含む三つの全二面へ制限する。
方針：元の零頂点と面の厳密な可換式を、既存の相対延長の制限へ渡す。
規約：全パラメータと指定比較を保持。使われ方：単位三単体の三関係の共通選択空間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 零頂点を含む三つの二面の最初の頂点は、元の三単体の同じ零頂点。 -/
lemma tetrahedronFace_initial (j : Fin 4) (hj : j ≠ 0) :
    scaffoldFirstVertex.{u} 2 ≫ stdSimplex.δ j = scaffoldFirstVertex 3 := by
  apply SSet.yonedaEquiv.injective
  fin_cases j
  · exact (hj rfl).elim
  all_goals
    apply SSet.stdSimplex.ext
    intro k
    rfl

/-- 任意の係数付きでも、同じ零頂点と元の二面は厳密に可換する。 -/
lemma tetrahedronFace_initial_prism (A : SSet.{u}) (j : Fin 4) (hj : j ≠ 0) :
    (scaffoldFirstVertex 2 ▷ A) ≫ (stdSimplex.δ j ▷ A) =
      𝟙 ((Δ[0] : SSet.{u}) ⊗ A) ≫ (scaffoldFirstVertex 3 ▷ A) := by
  rw [← comp_whiskerRight, tetrahedronFace_initial j hj, Category.id_comp]

variable {A E B : SSet.{u}} (p : E ⟶ B) (b : (Δ[3] : SSet.{u}) ⊗ A ⟶ B)
  (v : (Δ[0] : SSet.{u}) ⊗ A ⟶ E)
  (hv : v ≫ p = (scaffoldFirstVertex 3 ▷ A) ≫ b)

/-- 元の全三単体を同じ零頂点を持つ元の全二面へ制限する射。 -/
def tetrahedronFaceExtensionRestriction (j : Fin 4) (hj : j ≠ 0) :=
  relativeExtensionRestriction p b (scaffoldFirstVertex 3 ▷ A) v hv
    (stdSimplex.δ j ▷ A) (𝟙 _) (scaffoldFirstVertex 2 ▷ A)
    (tetrahedronFace_initial_prism A j hj)

/-- 制限先は元の全二面と元の初期値を固定した可縮な延長空間。 -/
lemma tetrahedronFaceExtensionRestriction_contractible [LeftFibration p]
    (j : Fin 4) (hj : j ≠ 0) :
    IsContractibleKan (relativeFunctorExtensionSpace p ((stdSimplex.δ j ▷ A) ≫ b)
      (scaffoldFirstVertex 2 ▷ A) (𝟙 _ ≫ v)
      (by rw [Category.assoc, hv, ← Category.assoc,
        ← tetrahedronFace_initial_prism A j hj, Category.assoc])) :=
  relativeFunctorExtensionSpace_isContractibleKan p _ _
    (leftAnodyneExtensions_whiskerRight _ (scaffoldFirstVertex_leftAnodyne 2) A) _ _

end SerrePositivity.InfinityCategories.F2
