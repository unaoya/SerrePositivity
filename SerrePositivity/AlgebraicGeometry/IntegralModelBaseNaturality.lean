module

public import SerrePositivity.AlgebraicGeometry.IntegralModelSpec

/-!
概要：I04 の各模型から元の基底への写像を、実際の図式の自然変換としてまとめる。
方針：模型の射の R-代数性と、既存の cone の射影の可換式を使う。
規約：自然性・合成の法則。新しい模型の存在は仮定しない。
使われ方：A07 の元の X への Spec R 上の因子化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- I04 の基底への構造射は、実際の模型の全ての遷移と可換。 -/
theorem integralModelSpecBaseMap_naturality
    {j k : (IntegralModelIndex R B)ᵒᵖ} (f : j ⟶ k) :
    (integralModelSpecDiagram R B).map f ≫ integralModelSpecBaseMap R B k.unop =
      integralModelSpecBaseMap R B j.unop := by
  change Spec.map ((integralModelSmallDiagram R B).map f.unop) ≫
    integralModelSpecBaseMap R B k.unop = integralModelSpecBaseMap R B j.unop
  dsimp only [integralModelSpecBaseMap]
  rw [← Spec.map_comp]
  congr 1
  ext z
  exact (((equivSmallModel (IntegralModelCategory R B)).inverse.map f.unop).hom.left.hom.hom).commutes z

/-- I04 の実際の図式を元の Spec R の上の図式にする自然変換。 -/
def integralModelSpecBaseNatTrans : integralModelSpecDiagram R B ⟶
    (Functor.const (IntegralModelIndex R B)ᵒᵖ).obj (Spec (CommRingCat.of R)) where
  app j := integralModelSpecBaseMap R B j.unop
  naturality j k f := by simpa using integralModelSpecBaseMap_naturality R B f

/-- I04 の cone は、元の Spec B→Spec R の上で可換。 -/
theorem integralModelSpecCone_base (j : (IntegralModelIndex R B)ᵒᵖ) :
    (integralModelSpecCone R B).π.app j ≫ (integralModelSpecBaseNatTrans R B).app j =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  integralModelSpecCone_projection_comp R B j.unop

end SerrePositivity.AlgebraicGeometry
