module

public import SerrePositivity.AlgebraicGeometry.CoefficientSpecLimit

/-!
概要：有限生成係数部分代数を、実際の有限係数図式の段へ同じ包含で因子化する。
方針：有限生成の証人の有限集合を取り、部分代数の包含の Spec を使う。
規約：元の環への忠実平坦性・Noether 性は要求しない。
使われ方：G2 の共通係数模型を、具体的な係数図式の後の段へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 有限生成係数部分代数への構造射は、具体的な係数図式の実際の段で因子化する。 -/
theorem exists_coefficient_spec_factor_of_fg
    (k : Type v) (R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (A : Subalgebra k R) (hA : A.FG) :
    ∃ (s : Finset R) (γ : (coefficientSpecDiagram k R).obj (.op s) ⟶ Spec (CommRingCat.of A)),
      (coefficientSpecCone k R).π.app (.op s) ≫ γ =
        Spec.map (CommRingCat.ofHom (algebraMap A R)) := by
  obtain ⟨s, hs⟩ := hA
  let q := Subalgebra.inclusion hs.ge
  refine ⟨s, Spec.map (CommRingCat.ofHom q.toRingHom), ?_⟩
  rw [coefficientSpecCone_projection, ← Spec.map_comp]
  congr 1

end SerrePositivity.AlgebraicGeometry
