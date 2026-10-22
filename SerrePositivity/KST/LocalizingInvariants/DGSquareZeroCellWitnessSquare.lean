module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare

/-!
概要：全射準同型上の並行な cell 比較を、class 射で相対 class 二重経路へ移す。
方針：端点固定の実 cell 充填を後合成し、内部両端と底への全経路を保持する。
規約：cell augmentation を一度前合成する。使われ方：class 輸送の coherence の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
open DGAlgebra
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  {f g : W ⟶ C} (v w : DGAlgebra.Path.Witness R f g)
  (hv : v.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (hw : w.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (N : Bimod B B) (κ : C ⟶ algebra B N) (hκ : κ ≫ projection B N = p)

def cellClassWitness : RelativeWitness (cellAugmentation R W ≫ f ≫ p) N
    (cellAugmentation R W ≫ f ≫ κ) (cellAugmentation R W ≫ g ≫ κ) where
  hom := cellAugmentation R W ≫ v.hom ≫ DGAlgebra.Path.map R κ
  source_eq := by
    rw [Category.assoc, Category.assoc, DGAlgebra.Path.map_source,
      ← Category.assoc v.hom, v.source_eq]
  target_eq := by
    rw [Category.assoc, Category.assoc, DGAlgebra.Path.map_target,
      ← Category.assoc v.hom, v.target_eq]
  projection_eq := by
    rw [Category.assoc, Category.assoc, ← DGAlgebra.Path.map_comp, hκ, hv]
    simp only [Category.assoc]

def cellClassWitnessSquare : RelativeWitnessSquare
    (cellClassWitness R p v hv N κ hκ) (cellClassWitness R p w hw N κ hκ) where
  hom := (RelativePath.cellSquareWitness R p hs hq v w hv hw).hom ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R κ)
  source_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_source, ← Category.assoc,
      (RelativePath.cellSquareWitness R p hs hq v w hv hw).source_eq]
    rfl
  target_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_target, ← Category.assoc,
      (RelativePath.cellSquareWitness R p hs hq v w hv hw).target_eq]
    rfl
  source_trace := by
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.map_source,
      DGAlgebra.Path.map_comp, ← Category.assoc, RelativePath.cellSquareWitness_source_trace]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality]
  target_trace := by
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.map_target,
      DGAlgebra.Path.map_comp, ← Category.assoc, RelativePath.cellSquareWitness_target_trace]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality]
  projection_eq := by
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_comp, hκ,
      RelativePath.cellSquareWitness_base_trace]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
