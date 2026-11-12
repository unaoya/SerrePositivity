module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedHomFunctor
/-!
概要：元の導来 kernel の射作用と指定 raw factor の自然性を証明する。
方針：同じ共役表示から全関手圏値関手の自然同型を構成する。
規約：可逆性を仮定しない。使われ方：ξ と κ の任意双加群射への自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
def dgKernelDerivedRawFactorNatIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E ≅ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolvedRawFunctorHomFunctor R D E :=
  NatIso.ofComponents (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedRawFactorIso R D E) (by
    intro P Q f
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
lemma dgKernelDerivedFunctorHomFunctor_rawFactor_square
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedRawFactorIso R D E Q).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedRawFactorIso R D E P).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolvedRawFunctorHomFunctor R D E).map f :=
  (dgKernelDerivedRawFactorNatIso R D E).hom.naturality f
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
