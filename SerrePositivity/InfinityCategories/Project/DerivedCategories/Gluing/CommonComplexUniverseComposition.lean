module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseHomInputFactor
/-!
概要：三つの対象宇宙を経る複体 Hom 模型の変更を一段の標準変更へまとめる。
方針：同じ全線形成分への単射性で、二段の変更が成分を変えないことを照合する。
規約：共通単体宇宙と元の複体を保持する。
使われ方：元左右 Hom 入力の導来二作用を正本の作用へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] (K : _root_.SerrePositivity.DifferentialGraded.Complex R)
lemma dgGluingCommonComplexUniverse_comp :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,v,w,max t r} K).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,w,t,max v r} K).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,v,t,max w r} K).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u,t} K)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget.{u,t} K) n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u,w,t} K n.unop.len
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u,v,w} K n.unop.len a.down)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u,v,t} K n.unop.len a.down)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear]

lemma dgGluingCommonComplexUniverse_map_triangle {L : _root_.SerrePositivity.DifferentialGraded.Complex R} (φ : K ⟶ L) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,v,w,max t r} K).hom ≫
      (SSet.uliftFunctor.{max u v w t r,max u w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,w} φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,w,t,max v r} L).hom =
    (SSet.uliftFunctor.{max u v w t r,max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,v} φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,v,t,max w r} L).hom := by
  rw [← reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso_naturality.{u,v,w,max t r} φ,
    dgGluingCommonComplexUniverse_comp.{u,v,w,t,r}]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
