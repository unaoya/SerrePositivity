module
public import SerrePositivity.DifferentialGraded.Presentation.ComplexCode
public import Mathlib.LinearAlgebra.Isomorphisms
/-!
概要：固定自由加群から各次数への全射を持つ複体を、関係と微分の小さいコードへ戻す。
方針：各次数の核による商の同型で微分を共役し、同じ全次数の複体同型を構成する。
規約：各次数の生成元被覆は入力に保持し、任意の複体が κ で生成されるとは主張しない。
使われ方：c′ の係数閉包を出発 dg 圏の固定基底 Hom 提示へ符号化する準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R] (B : Type u) (X : Complex R)
  (q : ∀ n : ℤ, (B →₀ R) →ₗ[R] X.X n) (hq : ∀ n, Function.Surjective (q n))

namespace DGComplexPresentationCode

def quotientComponentIso (n : ℤ) :
    ModuleCat.of R ((B →₀ R) ⧸ LinearMap.ker (q n)) ≅ X.X n :=
  ((q n).quotKerEquivOfSurjective (hq n)).toModuleIso

def ofSurjections : DGComplexPresentationCode R B where
  relations n := LinearMap.ker (q n)
  differential n := (quotientComponentIso R B X q hq n).hom ≫ X.d n (n + 1) ≫
    (quotientComponentIso R B X q hq (n + 1)).inv
  square n := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (X.d n (n + 1)), X.d_comp_d, zero_comp, comp_zero]

def ofSurjectionsIso : (ofSurjections R B X q hq).value R B ≅ X := by
  refine HomologicalComplex.Hom.isoOfComponents (quotientComponentIso R B X q hq) ?_
  intro i j hij
  have hj : i + 1 = j := hij
  subst j
  dsimp only [value]
  rw [CochainComplex.of_d]
  dsimp only [ofSurjections]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end DGComplexPresentationCode
end SerrePositivity.DifferentialGraded
