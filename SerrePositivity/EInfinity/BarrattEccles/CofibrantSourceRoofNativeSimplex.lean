module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismSimplex
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofPrefixPath

/-!
# 実 cofibrant comma の元の混合 coherent 錐単体

概要：任意可換環の実図式・評価・右脚を同じ混合 coherent 図式へ代入する。
方針：元の Kan hammock の豊穣関手を使い、最後の頂点を同じ qY へ同定する。
規約：元の全 path・時間・cofibrantHammockVertex を保持する。
使われ方：native roof 全三角形の実 slice prism の各単体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofProductCommaNativeSimplex {n : ℕ}
    (Γ : Fin (n + 1) ⥤ cofibrantSourceRoofProductComma A X Y b)
    (t : Fin (n + 1) →o Fin 2) :
    (kanHammockNerve (cofibrantAlgebraRelativeCategory A)) _⦋n + 1⦌ :=
  RoofPrefix.simplex (cofibrantAlgebraRelativeCategory A)
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f) Γ t

lemma cofibrantSourceRoofProductCommaNativeSimplex_target {n : ℕ}
    (Γ : Fin (n + 1) ⥤ cofibrantSourceRoofProductComma A X Y b)
    (t : Fin (n + 1) →o Fin 2) :
    (kanHammockNerve (cofibrantAlgebraRelativeCategory A)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op
      (cofibrantSourceRoofProductCommaNativeSimplex A X Y b Γ t) =
      cofibrantHammockVertex A Y :=
  (RoofPrefix.simplex_target (cofibrantAlgebraRelativeCategory A)
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f) Γ t).trans
      (hammockLocalizationNerveMap_vertex (cofibrantAlgebraRelativeCategory A)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)).symm

def cofibrantSourceRoofProductCommaNativeSliceSimplex {n : ℕ}
    (Γ : Fin (n + 1) ⥤ cofibrantSourceRoofProductComma A X Y b)
    (t : Fin (n + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (cofibrantHammockVertex A Y))) _⦋n⦌ := by
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    (cofibrantSourceRoofProductCommaNativeSimplex A X Y b Γ t), ?_⟩
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr,
    SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (fun z : (kanHammockNerve (cofibrantAlgebraRelativeCategory A)) _⦋0⦌ =>
    SSet.yonedaEquiv.symm z) (cofibrantSourceRoofProductCommaNativeSimplex_target A X Y b Γ t)

end SerrePositivity.EInfinity.BarrattEccles
