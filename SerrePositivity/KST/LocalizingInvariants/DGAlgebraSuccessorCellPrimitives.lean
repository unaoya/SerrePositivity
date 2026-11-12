module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInitialCellAlgebraLift
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Path

/-!
概要：全射準同型を通る段階代数射から、次段の全 cell の実原始元を構成する。
方針：一対象の段階 dg 関手を作り、指定境界と増大の値を同時に持ち上げる。
規約：元の対象型の instance を局所的なデータとして保持する。使われ方：cell 延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGCategoryCellResolution
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}

def cellStageLiftHom (n : ℕ) (g : cellStage R B n ⟶ C)
    (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) :
    (stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n).category.Hom x y ⟶ C.X := by
  cases x; cases y; exact g.hom

def cellStageLiftFunctor (n : ℕ) (g : cellStage R B n ⟶ C) :
    letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) := (stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n).category
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C) := by
  let S := stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n
  let m : ∀ x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B, S.category.Hom x y ⟶ C.X := cellStageLiftHom R n g
  have hi : ∀ x, S.category.id x ≫ m x x = η[C.X] := by
    intro x; cases x; exact IsMonHom.one_hom g.hom
  have hc : ∀ x y z, S.category.comp x y z ≫ m x z = (m x y ⊗ₘ m y z) ≫ μ[C.X] := by
    intro x y z; cases x; cases y; cases z; exact IsMonHom.mul_hom g.hom
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) := S.category
  exact { obj := fun _ => .star, map := m, map_id := hi, map_comp := hc }

variable (p : C ⟶ B) (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  (n : ℕ) (g : cellStage R B n ⟶ C) (hg : g ≫ p = cellStageAugmentation R B n)

include hs hq hg in
lemma cellStage_cell_primitive_exists (i : (stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n).CellIndex) :
    ∃ t : C.X.X i.2.2.degree,
      C.X.d i.2.2.degree (i.2.2.degree + 1) t =
        (cellStageLiftHom R n g i.1 i.2.1).f
          (i.2.2.degree + 1) i.2.2.cycle.val ∧
        p.hom.f i.2.2.degree t = i.2.2.primitive := by
  rcases i with ⟨x, y, c⟩
  cases x; cases y
  exact cellStage_relative_primitive_lift R p hs hq n g hg c

def successorCellPrimitives :
    let S := stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n
    let SI := S.CellIndex
    let SC := S.cells
    letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) := S.category
    DGCellAttachment.Family.PrimitiveData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) SI SC
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C) (cellStageLiftFunctor R n g) := by
  let h := cellStage_cell_primitive_exists R p hs hq n g hg
  let S := stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) := S.category
  exact { primitive := fun i => Classical.choose (h i)
          boundary := fun i => (Classical.choose_spec (h i)).1 }

include hs hq hg in
lemma successorCellPrimitives_projection (i : (stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n).CellIndex) :
    let S := stage R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n
    let P := successorCellPrimitives R p hs hq n g hg
    letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) := S.category
    p.hom.f i.2.2.degree (P.primitive i) = i.2.2.primitive :=
  (Classical.choose_spec (cellStage_cell_primitive_exists R p hs hq n g hg i)).2

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
