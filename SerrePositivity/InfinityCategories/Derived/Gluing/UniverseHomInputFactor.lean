module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomModelNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R]
lemma dgGluingCommonComplexPinchedUniverseIso_naturality {K L : Complex R} (φ : K ⟶ L) :
    (SSet.uliftFunctor.{max u v w r, max u v}).map (complexPinchedMap.{u, v} φ) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} L).hom =
    (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} K).hom ≫
      (SSet.uliftFunctor.{max u v w r, max u w}).map (complexPinchedMap.{u, w} φ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (linearEquiv (complexPinchedSource.{u, w} L)
    (complexPinchedTarget.{u, w} L) n.unop.len).injective
  change toLinearSimplex
      (dgGluingComplexPinchedUniverseEquiv.{u,v,w} L n.unop.len
        (pinchedHomChainMapSimplex _ s.down)) =
    toLinearSimplex (pinchedHomChainMapSimplex _
      (dgGluingComplexPinchedUniverseEquiv.{u,v,w} K n.unop.len s.down))
  rw [dgGluingComplexPinchedUniverseEquiv_linear, pinchedHomChainMapSimplex_linear,
    pinchedHomChainMapSimplex_linear, dgGluingComplexPinchedUniverseEquiv_linear]
  rfl
lemma dgGluingCommonComplexUniverse_hom_eq_hom (K : Complex R) :
    (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, max u v w} K).hom =
      (dgGluingComplexPinchedUniverseIso.{u, v, w} K).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl
variable {C : Type v} {D : Type w} [DGCategory R C] [DGCategory R D]
  {x y : C} {x' y' : D} {K : Complex R}
lemma dgGluingUniverseHomChainMap_input_factor (φ : homObject R C x y ⟶ K)
    (ψ : K ⟶ homObject R D x' y') :
    dgGluingUniverseHomChainMap.{u, v, w, max u v w r} (φ ≫ ψ) =
      (SSet.uliftFunctor.{max u v w r, max u v}).map (pinchedComplexModelIso x y).hom ≫
      (SSet.uliftFunctor.{max u v w r, max u v}).map (complexPinchedMap.{u, v} φ) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} K).hom ≫
      (SSet.uliftFunctor.{max u v w r, max u w}).map
        (complexPinchedMap.{u, w} ψ ≫ (pinchedComplexModelIso x' y').inv) := by
  apply (cancel_mono ((SSet.uliftFunctor.{max u v w r, max u w}).map
    (pinchedComplexModelIso x' y').hom)).mp
  rw [dgGluingUniverseHomModel_naturality.{u, v, w, r}]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id]
  rw [complexPinchedMap_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [dgGluingCommonComplexPinchedUniverseIso_naturality.{u, v, w, r}]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
end SerrePositivity.InfinityCategories
