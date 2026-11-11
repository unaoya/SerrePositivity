module

public import SerrePositivity.KST.Spectra.CoherentTrianglePathMaximum
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomComparison

/-!
概要：coherent nerve の二単体から Hom の経路を、三単体から Hom の正方形を取り出す。
方針：長い Hom を元の path の区間・正方形で制限する。
規約：単体や充填を選び直さない。使われ方：元の円評価の三単体から三角形の差を読む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の coherent 二単体の長い Hom の、元の path による経路。 -/
def triangleTrace (σ : (SimplicialNerve C) _⦋2⦌) :
    (Δ[1] : SSet.{u}) ⟶ SimplicialCategory.sHom (σ.obj ⟨ULift.up 0⟩) (σ.obj ⟨ULift.up 2⟩) :=
  trianglePathInterval ≫ σ.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩

/-- 元の coherent 三単体の長い Hom の、二つの内点に対応する元の正方形。 -/
def tetrahedronTrace (σ : (SimplicialNerve C) _⦋3⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      SimplicialCategory.sHom (σ.obj ⟨ULift.up 0⟩) (σ.obj ⟨ULift.up 3⟩) :=
  tetrahedronPathSquare ≫ σ.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩

/-- Hom 比較の二単体から経路を取り出すと、元の Hom の辺そのものに戻る。 -/
lemma triangleTrace_comparison {X Y : C} (a : (SimplicialCategory.sHom X Y) _⦋1⦌) :
    triangleTrace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex a) = SSet.yonedaEquiv.symm a := by
  change trianglePathInterval ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 2) ≫
    SSet.yonedaEquiv.symm a) = _
  rw [← Category.assoc, trianglePathInterval_maximum, Category.id_comp]

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
