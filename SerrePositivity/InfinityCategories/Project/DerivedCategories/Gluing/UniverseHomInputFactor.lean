module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseHomModelNaturality
/-! # 元入力を保持する一般宇宙の Hom 作用の因子分解

概要：複体を経る Hom 鎖写像を、元 Hom 模型・元入力・対象宇宙変更の順に分解する。
方針：Hom 模型の自然性と線形成分を変えない宇宙同型の自然性を使う。
規約：対象や複体を変更せず、Small 仮定を追加しない。
使われ方：native 標準面の可変入力を正本係数三角形の同じ入力へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]
lemma dgGluingCommonComplexPinchedUniverseIso_naturality {K L : _root_.SerrePositivity.DifferentialGraded.Complex R} (φ : K ⟶ L) :
    (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} L).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} K).hom ≫
      (SSet.uliftFunctor.{max u v w r, max u w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w} φ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u, w} L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget.{u, w} L) n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u,v,w} L n.unop.len
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex _ s.down)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u,v,w} K n.unop.len s.down))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear]
  rfl
lemma dgGluingCommonComplexUniverse_hom_eq_hom (K : _root_.SerrePositivity.DifferentialGraded.Complex R) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, v, w, max u v w} K).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso.{u, v, w} K).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl
variable {C : Type v} {D : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  {x y : C} {x' y' : D} {K : _root_.SerrePositivity.DifferentialGraded.Complex R}
lemma dgGluingUniverseHomChainMap_input_factor (φ : _root_.SerrePositivity.DifferentialGraded.homObject R C x y ⟶ K)
    (ψ : K ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D x' y') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, max u v w r} (φ ≫ ψ) =
      (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).hom ≫
      (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} K).hom ≫
      (SSet.uliftFunctor.{max u v w r, max u w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w} ψ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x' y').inv) := by
  apply (cancel_mono ((SSet.uliftFunctor.{max u v w r, max u w}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x' y').hom)).mp
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomModel_naturality.{u, v, w, r}]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [dgGluingCommonComplexPinchedUniverseIso_naturality.{u, v, w, r}]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
