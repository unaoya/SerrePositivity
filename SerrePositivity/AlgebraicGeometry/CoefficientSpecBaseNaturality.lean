module

public import SerrePositivity.AlgebraicGeometry.CoefficientSpecLimit

/-!
概要：実際の係数部分代数の Spec の図式を、同じ係数基底の上へ送る。
方針：構造環準同型と各包含の可換式を Spec の合成で照合する。
規約：係数環とスキームの宇宙をそろえて使う。
使われ方：B02・B03 の細分の射を同じ係数基底上で因子化する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

/-- 実際の係数図式の各段から、同じ係数基底への自然変換。 -/
def coefficientSpecBaseNatTrans : coefficientSpecDiagram k R ⟶
    (Functor.const (Finset R)ᵒᵖ).obj (Spec (CommRingCat.of k)) where
  app j := Spec.map (CommRingCat.ofHom (algebraMap k (Algebra.adjoin k (j.unop : Set R))))
  naturality i j g := by
    dsimp [coefficientSpecDiagram, coefficientSubalgebraDiagram]
    rw [← Spec.map_comp]
    congr 1

/-- 元の Spec R の cone は、係数基底の上で可換。 -/
theorem coefficientSpecCone_base (j : (Finset R)ᵒᵖ) :
    (coefficientSpecCone k R).π.app j ≫ (coefficientSpecBaseNatTrans k R).app j =
      Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
  change Spec.map (CommRingCat.ofHom (Algebra.adjoin k (j.unop : Set R)).val.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (Algebra.adjoin k (j.unop : Set R)))) = _
  rw [← Spec.map_comp]
  congr 1

end SerrePositivity.AlgebraicGeometry
