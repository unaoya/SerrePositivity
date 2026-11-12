module

public import SerrePositivity.EInfinity.PowerOperation.CyclicTateComplex
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# 自明係数とのテンソルによる同じ周期微分の比較

DAG XIII Proposition 2.2.3 の混合軌道の Tate 消滅に使う係数側の補助。
ノルムと作用差を、自明表現とのテンソルで移す。
同じ微分の厳密な比較であり、ホモロジー上の式で代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]
variable (A B : Rep.{u} k G) [B.IsTrivial]

/-- 自明表現との右テンソルは、同じ指定周期微分を保つ。 -/
lemma cyclicTateDifferential_tensorTrivial (g : G) (i : ℤ) :
    (tensorRight B).map (cyclicTateDifferential A g i) =
      cyclicTateDifferential (A ⊗ B) g i := by
  by_cases hi : Even i
  · simp only [cyclicTateDifferential, ite_eq_left hi, Functor.map_sub]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    simp [Rep.sub_hom, Rep.applyAsHom, Representation.tprod_apply,
      Representation.isTrivial_apply]
  · simp only [cyclicTateDifferential, ite_eq_right hi]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    simp [Rep.norm, Representation.norm, Representation.tprod_apply,
      Representation.isTrivial_apply, TensorProduct.sum_tmul]

/-- 元の周期複体の右テンソルと、同じ対角作用の周期複体の指定同型。 -/
def cyclicTateComplex_tensorTrivialIso (g : G) :
    ((tensorRight B).mapHomologicalComplex (.up ℤ)).obj (cyclicTateComplex A g) ≅
      cyclicTateComplex (A ⊗ B) g :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j h
    change i + 1 = j at h
    subst j
    simpa [cyclicTateComplex, CochainComplex.of.d] using
      (cyclicTateDifferential_tensorTrivial A B g i).symm)

end SerrePositivity.EInfinity.PowerOperation
