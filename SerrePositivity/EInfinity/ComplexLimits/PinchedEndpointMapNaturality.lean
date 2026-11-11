module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.PinchedEndpointTransport

/-!
# 端点の等式輸送と元の pinched Hom 関手作用

概要：同じ端点の等式を前後どちらで輸送しても元の関手作用を回収する。
方針：二つの端点等式への帰納法を使う。
規約：端点の等式による輸送と頂点同型の作用を区別する。
使われ方：K-projective 包含後の実導来 Hom 比較の端点の照合。
-/

@[expose] public section
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

lemma pinchedEndpointIso_map {C D : SSet.{u}} (F : C ⟶ D)
    {x y x' y' : C.obj (Opposite.op (SimplexCategory.mk 0))} (hx : x = x') (hy : y = y') :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso hx hy).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x' y' =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x y ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
      (congrArg (F.app (Opposite.op (SimplexCategory.mk 0))) hx)
      (congrArg (F.app (Opposite.op (SimplexCategory.mk 0))) hy)).hom := by
  subst x'
  subst y'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso, Iso.refl_hom, Category.id_comp, Category.comp_id]

end SerrePositivity.EInfinity.ComplexLimits
