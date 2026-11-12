module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.InputFunctor
public import SerrePositivity.KST.SConstruction.DGFunctorNativeComposition

/-!
概要：入力関手圏の native Kan core の全単体を、新閉包関手圏の core へ送る。
方針：全次数入力関手の dg nerve を取り、最大 Kan 部分へ制限する。
規約：cone 段階の全 native Hom 作用。平坦分解・商の作用や横合成則は別工程。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C D : Type (max (u + 1) v))
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_small

/-- cone の固定代表間で、入力 Kan core の全高次単体へ作用する。 -/
def dgKappaSphereClosureNativeHom :
    dgFunctorNativeMappingSpace R C D ⟶
      dgFunctorNativeMappingSpace R {M // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R C κ M}
        {N // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ N} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionInputFunctor R C D hκ hreg))

/-- 零単体の作用は、D-3 の同じ固定閉包関手。 -/
lemma dgKappaSphereClosureNativeHom_vertex (F : DGFunctor R C D) :
    (dgKappaSphereClosureNativeHom R C D hκ hreg).app (Opposite.op ⦋0⦌)
      (dgFunctorNativeMappingVertex R C D F) =
    dgFunctorNativeMappingVertex R _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D F hκ hreg) := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
