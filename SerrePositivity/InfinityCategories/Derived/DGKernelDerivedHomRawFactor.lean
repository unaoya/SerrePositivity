module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedHomFunctor
/-!
概要：元の導来 kernel の射作用と指定 raw factor の自然性を証明する。
方針：同じ共役表示から全関手圏値関手の自然同型を構成する。
規約：可逆性を仮定しない。使われ方：ξ と κ の任意双加群射への自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
def dgKernelDerivedRawFactorNatIso :
    dgKernelDerivedFunctorHomFunctor R D E ≅ dgKernelResolvedRawFunctorHomFunctor R D E :=
  NatIso.ofComponents (dgKernelDerivedRawFactorIso R D E) (by
    intro P Q f
    dsimp only [dgKernelDerivedFunctorHomFunctor]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
lemma dgKernelDerivedFunctorHomFunctor_rawFactor_square
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q) :
    (dgKernelDerivedFunctorHomFunctor R D E).map f ≫
      (dgKernelDerivedRawFactorIso R D E Q).hom =
    (dgKernelDerivedRawFactorIso R D E P).hom ≫
      (dgKernelResolvedRawFunctorHomFunctor R D E).map f :=
  (dgKernelDerivedRawFactorNatIso R D E).hom.naturality f
end
end SerrePositivity.InfinityCategories
