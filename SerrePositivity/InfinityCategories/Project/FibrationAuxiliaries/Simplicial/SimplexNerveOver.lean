module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldFiniteNerveUniverse
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：通常圏の nerve に入る元の標準単体を、同じ有限鎖の関手と底上で同一視する。
方針：標準単体と有限鎖の nerve の同型に、nerve 関手の充満忠実性を適用する。
規約：元の単体写像を底上の同型の可換式で保持する。
使われ方：任意の標準面上の native Hom に、同じ有限セルの分類比較を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
variable {C : Type u} [Category.{u} C] {n : ℕ} (σ : (Δ[n] : SSet.{u}) ⟶ nerve C)

/-- 元の標準単体と同じ nerve 写像を持つ有限鎖の関手。 -/
def simplexNerveBaseFunctor : ULift.{u} (Fin (n + 1)) ⥤ C :=
  (nerveFunctor.preimage (show
    nerveFunctor.obj (Cat.of (ULift.{u} (Fin (n + 1)))) ⟶ nerveFunctor.obj (Cat.of C) from
      (stdSimplex.isoNerve.{u} n).inv ≫ σ)).toFunctor

/-- 同じ有限鎖の関手の nerve は、元の標準単体そのものを回収する。 -/
lemma simplexNerveBaseFunctor_nerveMap :
    nerveMap (simplexNerveBaseFunctor σ) = (stdSimplex.isoNerve.{u} n).inv ≫ σ := by
  unfold simplexNerveBaseFunctor
  exact nerveFunctor.map_preimage (show
    nerveFunctor.obj (Cat.of (ULift.{u} (Fin (n + 1)))) ⟶ nerveFunctor.obj (Cat.of C) from
      (stdSimplex.isoNerve.{u} n).inv ≫ σ)

/-- 元の標準単体と同じ有限鎖の表示の、元の底上の同型。 -/
def simplexNerveOverIso : Over.mk σ ≅ Over.mk (nerveMap (simplexNerveBaseFunctor σ)) :=
  Over.isoMk (stdSimplex.isoNerve.{u} n) (by
    change (stdSimplex.isoNerve.{u} n).hom ≫ nerveMap (simplexNerveBaseFunctor σ) = σ
    rw [simplexNerveBaseFunctor_nerveMap, Iso.hom_inv_id_assoc])

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
