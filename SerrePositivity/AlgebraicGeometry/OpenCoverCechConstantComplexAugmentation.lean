module

public import SerrePositivity.AlgebraicGeometry.CechConstantComplexAugmentation
public import SerrePositivity.AlgebraicGeometry.OpenCoverCech

/-!
概要：同じ全次数の増大を、元の開の前層の実際の切断へ代入する。
方針：空交叉への元の制限に、全タプルの同じ定数増大を合成する。
規約：元の全空間の値・タプルの有限像・制限の写像を保持する。
使われ方：元の構造層のFrobenius係数による定数増大列への入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v w
variable {X : Type u} [TopologicalSpace X] {R : Type w} [CommRing R]
variable {ι : Type} [DecidableEq ι]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) (U : ι → Opens X)
variable (A : ModuleCat.{v} R) (α : A ⟶ P.obj (op ⊤))

/-- 元の空交叉への制限から作る、全次数の同じ定数増大。 -/
def openCoverCechConstantComplexAugmentation :
    cechConstantComplex A ⟶ fullCechComplex (openCoverCechDiagram P U) :=
  fullCechConstantComplexAugmentation (openCoverCechDiagram P U) A
    (α ≫ P.map (homOfLE (show cechOpenIntersection U ∅ ≤ ⊤ from le_top)).op)

set_option backward.isDefEq.respectTransparency false in
/-- 各タプルでの値は、元の全空間から同じ実際の交叉への制限。 -/
theorem openCoverCechConstantComplexAugmentation_apply (n : ℕ) (x : A)
    (t : Fin (n + 1) → ι) :
    ((openCoverCechConstantComplexAugmentation P U A α).f n).hom x t =
      (P.map (homOfLE (show cechOpenIntersection U (cechTupleSupport t) ≤ ⊤
        from le_top)).op).hom (α.hom x) := by
  have h := fullCechConstantComplexAugmentation_apply (openCoverCechDiagram P U) A
    (α ≫ P.map (homOfLE (show cechOpenIntersection U ∅ ≤ ⊤ from le_top)).op) n x t
  refine h.trans ?_
  change (P.map (homOfLE (cechOpenIntersection_antitone U
      (Finset.empty_subset (cechTupleSupport t)))).op).hom
      ((P.map (homOfLE (show cechOpenIntersection U ∅ ≤ ⊤ from le_top)).op).hom
        (α.hom x)) = _
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← P.map_comp]
  rfl

end SerrePositivity.AlgebraicGeometry
