module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.IdentityHomTargetDiagonal
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetContraction
public import SerrePositivity.KST.SConstruction.DGHomGluingConeFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ContractingZeroVertex
/-!
概要：恒等 Hom gluing の元対角を、同じ実 cone 関手が native perfect 圏で零化する。
方針：同じ恒等閉比較の既存収縮元を全 Hom と微分を変えずに使う。
規約：零化だけの判定。全 cone 関手比較は局所化判定へ別に接続する。
使われ方：恒等 cone 差の対角零化条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet DifferentialGraded KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
local notation "I" => _root_.SerrePositivity.DifferentialGraded.DGFunctor.id (A := R) C
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingIdentityConeDiagonal_vertex_zero (x : C) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((dgHomGluingConeFunctor R C C C I I).obj
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonal.{u, 0} R C).obj x))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isZeroVertex _
    (dgHomGluingTargetConeContractingElement R C C C I I
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonal.{u, 0} R C).obj x) (Iso.refl _)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonal_targetMap.{u, 0} R C x))
  exact dgHomGluingTargetConeContractingElement_d R C C C I I
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonal.{u, 0} R C).obj x) (Iso.refl _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonal_targetMap.{u, 0} R C x)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
