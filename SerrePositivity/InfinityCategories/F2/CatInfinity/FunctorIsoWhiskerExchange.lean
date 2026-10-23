module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorCompositionWhiskerEdges
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：指定関手同型の前後合成の交換則。
方針：代表辺の積の正方形を関手空間の合成へ写す。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定関手同型の前後合成の交換則。
方針：代表辺の積の正方形を関手空間の合成へ写す。
規約：元の指定同型と辺の類を保持する。
使われ方：引き戻しの二射影の比較と指定 path の整合。 -/
lemma functorIso_whisker_exchange {X Y Z : SSet.{u}} [Quasicategory Y] [Quasicategory Z]
    {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (e : FunctorIso f₀ f₁) (d : FunctorIso g₀ g₁) :
    e.postcomp g₀ ≪≫ d.precomp f₁ = d.precomp f₀ ≪≫ e.postcomp g₁ := by
  apply Iso.ext
  change (e.postcomp g₀).hom ≫ (d.precomp f₁).hom =
    (d.precomp f₀).hom ≫ (e.postcomp g₁).hom
  rw [functorIso_postcomp_hom, functorIso_precomp_hom,
    functorIso_precomp_hom, functorIso_postcomp_hom,
    ← FunctorIso.edge_homMk e, ← FunctorIso.edge_homMk d]
  have h := congrArg
    (fun k ↦ (SSet.Truncated.mapHomotopyCategory
      ((truncation 2).map (MonoidalClosed.comp X Y Z))).map k)
    (SSet.Truncated.HomotopyCategory.BinaryProduct.square (FunctorIso.edge e) (FunctorIso.edge d))
  simp only [Functor.map_comp, SSet.Truncated.mapHomotopyCategory_homMk] at h
  have hs := homMk_square_of_edge_eq _ _ _ _
    ((FunctorIso.edge e).map ((truncation 2).map ((ihom X).map g₀)))
    ((FunctorIso.edge d).map ((truncation 2).map ((pre f₁).app Z)))
    ((FunctorIso.edge d).map ((truncation 2).map ((pre f₀).app Z)))
    ((FunctorIso.edge e).map ((truncation 2).map ((ihom X).map g₁))) h
    (functorComposition_post_edge _ _) (functorComposition_pre_edge _ _)
    (functorComposition_pre_edge _ _) (functorComposition_post_edge _ _)
  exact hs

end SerrePositivity.InfinityCategories.F2
