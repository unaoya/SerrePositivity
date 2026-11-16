module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CosimplicialComparison

/-!
# 元の交代余面複体の比較の合成則

## 概要
元の各項の恒等同型は、関手の合成と自然変換に関して可換となる。

## 方針
元の同じ非負次数の成分で検査する。

## 規約
関手の間の比較を再選択しない。

## 使われ方
HT04.R2の完備行と通常行の元の比較を接続する。
-/

public noncomputable section
universe u v
open CategoryTheory AlgebraicTopology HomologicalComplex
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTComparisonTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable [Preadditive C] [Preadditive D] [Preadditive E]

/-- 元の各項恒等の比較は関手の合成を保つ。 -/
theorem alternatingCofaceFunctorIso_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (X : CosimplicialObject C) :
    ((alternatingCofaceFunctorIso (F ⋙ G)).app X).hom =
      (G.mapHomologicalComplex (.up ℕ)).map ((alternatingCofaceFunctorIso F).app X).hom ≫
        ((alternatingCofaceFunctorIso G).app (X ⋙ F)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change 𝟙 _ = G.map (𝟙 _) ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

/-- 元の各項恒等の比較は自然変換と可換。 -/
theorem alternatingCofaceFunctorIso_natTrans {F G : C ⥤ D}
    [F.Additive] [G.Additive] (α : F ⟶ G) (X : CosimplicialObject C) :
    ((alternatingCofaceFunctorIso F).app X).hom ≫
      (alternatingCofaceMapComplex D).map (Functor.whiskerLeft X α) =
    (NatTrans.mapHomologicalComplex α (.up ℕ)).app
      ((alternatingCofaceMapComplex C).obj X) ≫
      ((alternatingCofaceFunctorIso G).app X).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change 𝟙 _ ≫ α.app (X.obj ⦋n⦌) = α.app (X.obj ⦋n⦌) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
