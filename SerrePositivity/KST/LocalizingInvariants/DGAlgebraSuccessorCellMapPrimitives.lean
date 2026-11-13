module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInitialCellMapLift
public import SerrePositivity.DifferentialGraded.Resolution.FixedObject

/-!
概要：任意の次段の代数射の指定原始元を保つ cell 延長の入力。
方針：元の付加生成元を標的射で送り、全射擬同型を通る境界充填を適用する。
規約：元の増大の値への持ち上げに限定しない。
使われ方：cell 分解からの任意射の全段持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGCategoryCellResolution
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)}

def cellMapGenerator (n : ℕ) (c : ComplexBoundaryCell R (cellStageAugmentation R A n).hom) :
    (cellStage R A (n + 1)).X.X c.degree :=
  (stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) n).cellGenerator ⟨.star, .star, c⟩

lemma cellMapGenerator_boundary (n : ℕ)
    (c : ComplexBoundaryCell R (cellStageAugmentation R A n).hom) :
    (cellStage R A (n + 1)).X.d c.degree (c.degree + 1) (cellMapGenerator R n c) =
      (cellStageTransition R A n).hom.f (c.degree + 1) c.cycle.val := by
  let S := stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) n
  let SC := S.cells
  let SI := S.CellIndex
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) := S.category
  exact SC.differential_generatorElement R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) SI
    ⟨.star, .star, c⟩

def cellMapBoundaryCell (n : ℕ) (b : cellStage R A (n + 1) ⟶ B)
    (c : ComplexBoundaryCell R (cellStageAugmentation R A n).hom) :
    ComplexBoundaryCell R ((cellStageTransition R A n).hom ≫ b.hom) where
  degree := c.degree
  cycle := c.cycle
  primitive := b.hom.f c.degree (cellMapGenerator R n c)
  boundary := by
    have h := congrArg (fun f => f (cellMapGenerator R n c))
      (b.hom.comm c.degree (c.degree + 1))
    change B.X.d c.degree (c.degree + 1) (b.hom.f c.degree (cellMapGenerator R n c)) =
      b.hom.f (c.degree + 1)
        ((cellStage R A (n + 1)).X.d c.degree (c.degree + 1) (cellMapGenerator R n c)) at h
    rw [cellMapGenerator_boundary] at h
    exact h

variable (p : C ⟶ B) (hs : ∀ k : ℤ, Function.Surjective (p.hom.f k))
  (hq : QuasiIso p.hom) (n : ℕ) (a : cellStage R A n ⟶ C)
  (b : cellStage R A (n + 1) ⟶ B) (ha : a ≫ p = cellStageTransition R A n ≫ b)

include hs hq ha in
lemma successorCellMapPrimitive_exists (i : (stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) n).CellIndex) :
    ∃ t : C.X.X i.2.2.degree,
      C.X.d i.2.2.degree (i.2.2.degree + 1) t =
        (cellStageLiftHom R n a i.1 i.2.1).f (i.2.2.degree + 1) i.2.2.cycle.val ∧
      p.hom.f i.2.2.degree t =
        (cellStageLiftHom R (n + 1) b i.1 i.2.1).f i.2.2.degree
          ((stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) n).cellGenerator i) := by
  rcases i with ⟨x, y, c⟩
  cases x; cases y
  exact cochain_relative_primitive_lift p.hom hs hq a.hom
    ((cellStageTransition R A n).hom ≫ b.hom) (congrArg Mon.Hom.hom ha)
    (cellMapBoundaryCell R n b c)

def successorCellMapPrimitives :
    let S := stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) n
    let SI := S.CellIndex
    let SC := S.cells
    letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) := S.category
    DGCellAttachment.Family.PrimitiveData R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) SI SC
      (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R C) (cellStageLiftFunctor R n a) := by
  let h := successorCellMapPrimitive_exists R p hs hq n a b ha
  let S := stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) n
  letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) := S.category
  exact { primitive := fun i => Classical.choose (h i)
          boundary := fun i => (Classical.choose_spec (h i)).1 }

lemma successorCellMapPrimitives_projection (i : (stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) n).CellIndex) :
    let S := stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) n
    let v := (cellStageLiftHom R (n + 1) b i.1 i.2.1).f i.2.2.degree (S.cellGenerator i)
    let P := successorCellMapPrimitives R p hs hq n a b ha
    letI : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R A) := S.category
    p.hom.f i.2.2.degree (P.primitive i) = v :=
  (Classical.choose_spec (successorCellMapPrimitive_exists R p hs hq n a b ha i)).2

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
