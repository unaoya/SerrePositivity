module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.InputParameter
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorEnrichment

/-!
概要：入力 dg 関手の全 Hom 作用を、新閉包の dg 関手圏への dg 関手として束ねる。
方針：各実加群での入力 Hom の単位・合成保存と実閉同型の相殺を使う。
規約：これは関手変数の縦合成に関する豊穣則。横合成の厳密一致は別工程。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_small

lemma dgKappaSphereClosureExtensionInputHom_identity (F : DGFunctor R C D) :
    dgFunctorIdentity R C D F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionInputHom R C D hκ hreg F F =
      dgFunctorIdentity R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D F hκ hreg) := by
  apply dgFunctorHom_ext
  intro M
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionInputHom_π, ← Category.assoc,
    dgModuleExtensionInputHom_identity, dgFunctorIdentity_π]
  exact enrichedClosedIsoConjugation_id (Complex R)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R C D F hκ hreg).iso M)

lemma dgKappaSphereClosureExtensionInputHom_composition (F G H : DGFunctor R C D) :
    dgFunctorComposition R C D F G H ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionInputHom R C D hκ hreg F H =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionInputHom R C D hκ hreg F G ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionInputHom R C D hκ hreg G H) ≫
      dgFunctorComposition R _ _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D F hκ hreg)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D G hκ hreg)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D H hκ hreg) := by
  apply dgFunctorHom_ext
  intro M
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionInputHom_π,
    dgFunctorComposition_π, tensorHom_comp_tensorHom_assoc]
  rw [← Category.assoc, dgModuleExtensionInputHom_composition, Category.assoc]
  rw [← tensorHom_comp_tensorHom_assoc]
  have hc := enrichedClosedIsoConjugation_comp (Complex R)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R C D F hκ hreg).iso M)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R C D G hκ hreg).iso M)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R C D H hκ hreg).iso M)
  exact congrArg (fun k =>
    (dgModuleExtensionInputHom R C D F G (ForgetEnrichment.to (Complex R) M.val) ⊗ₘ
      dgModuleExtensionInputHom R C D G H (ForgetEnrichment.to (Complex R) M.val)) ≫ k)
    hc.symm

/-- 新閉包に対する入力変数の全次数作用。native Hom 作用の cone 段階。 -/
def dgKappaSphereClosureExtensionInputFunctor :
    DGFunctor R (DGFunctor R C D)
      (DGFunctor R {M // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R C κ M}
        {N // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ N}) where
  obj F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D F hκ hreg
  map := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionInputHom R C D hκ hreg
  map_id := dgKappaSphereClosureExtensionInputHom_identity R C D hκ hreg
  map_comp := dgKappaSphereClosureExtensionInputHom_composition R C D hκ hreg

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
