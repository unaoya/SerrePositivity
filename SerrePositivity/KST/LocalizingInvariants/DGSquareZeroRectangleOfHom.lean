module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessRectangleTransport

/-!
概要：全底射影が定数の実二重経路から、四つの相対辺と正方形を回収する。
方針：四つの実評価と経路関手の自然性を使う。
規約：四辺の相対性を追加入力にしない。使われ方：元の classifying 正方形への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RectangleOfHom
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} (N : Bimod B B)
  (H : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)))

abbrev corner00 : W ⟶ algebra B N :=
  (H ≫ DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra B N))) ≫
    DGAlgebra.Path.source R (algebra B N)
abbrev corner01 : W ⟶ algebra B N :=
  (H ≫ DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra B N))) ≫
    DGAlgebra.Path.target R (algebra B N)
abbrev corner10 : W ⟶ algebra B N :=
  (H ≫ DGAlgebra.Path.target R (DGAlgebra.Path.algebra R (algebra B N))) ≫
    DGAlgebra.Path.source R (algebra B N)
abbrev corner11 : W ⟶ algebra B N :=
  (H ≫ DGAlgebra.Path.target R (DGAlgebra.Path.algebra R (algebra B N))) ≫
    DGAlgebra.Path.target R (algebra B N)

variable (q : W ⟶ B)
  (hbase : H ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
    (q ≫ DGAlgebra.Path.diagonal R B) ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R B))

def outerSource : RelativeWitness q N (corner00 N H) (corner01 N H) where
  hom := H ≫ DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra B N))
  source_eq := rfl
  target_eq := rfl
  projection_eq := by
    rw [Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc, hbase,
      Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id]

def outerTarget : RelativeWitness q N (corner10 N H) (corner11 N H) where
  hom := H ≫ DGAlgebra.Path.target R (DGAlgebra.Path.algebra R (algebra B N))
  source_eq := rfl
  target_eq := rfl
  projection_eq := by
    rw [Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc, hbase,
      Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id]

def innerSource : RelativeWitness q N (corner00 N H) (corner10 N H) where
  hom := H ≫ DGAlgebra.Path.map R (DGAlgebra.Path.source R (algebra B N))
  source_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_source, ← Category.assoc]
  target_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_target, ← Category.assoc]
  projection_eq := by
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_source,
      DGAlgebra.Path.map_comp, ← Category.assoc, hbase, Category.assoc,
      DGAlgebra.Path.diagonal_naturality, ← Category.assoc,
      Category.assoc q, DGAlgebra.Path.diagonal_source, Category.comp_id]

def innerTarget : RelativeWitness q N (corner01 N H) (corner11 N H) where
  hom := H ≫ DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra B N))
  source_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_source, ← Category.assoc]
  target_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_target, ← Category.assoc]
  projection_eq := by
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_target,
      DGAlgebra.Path.map_comp, ← Category.assoc, hbase, Category.assoc,
      DGAlgebra.Path.diagonal_naturality, ← Category.assoc,
      Category.assoc q, DGAlgebra.Path.diagonal_target, Category.comp_id]

/-- 同じ実二重経路を四つの相対辺とともに保持する。 -/
def rectangle : RelativeWitnessRectangle (outerSource N H q hbase) (outerTarget N H q hbase)
    (innerSource N H q hbase) (innerTarget N H q hbase) where
  hom := H
  source_eq := rfl
  target_eq := rfl
  source_trace := rfl
  target_trace := rfl
  projection_eq := hbase

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RectangleOfHom
