module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismNaturality
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativeSimplex

/-!
# 元の実 comma から同じ qY slice への native 全 prism

概要：元の混合単体を全ての面・退化に整合する一つの slice 写像へ束ねる。
方針：最後の頂点固定延長の自然性と join の標準同型を使う。
規約：任意可換環・元の qY・全パラメータ・同じ混合単体を保持する。
使われ方：native roof 全三角形の slice prism 本体。両端と底の同定は後続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductCommaNativeSimplex_naturality {m n : ℕ}
    (Γ : Fin (n + 1) ⥤ cofibrantSourceRoofProductComma A X Y b)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (cofibrantAlgebraRelativeCategory A)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).op
      (cofibrantSourceRoofProductCommaNativeSimplex A X Y b Γ t) =
    cofibrantSourceRoofProductCommaNativeSimplex A X Y b
      (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.simplex_naturality (cofibrantAlgebraRelativeCategory A)
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f) Γ t α

lemma cofibrantSourceRoofProductCommaNativeSliceSimplex_naturality {m n : ℕ}
    (Γ : Fin (n + 1) ⥤ cofibrantSourceRoofProductComma A X Y b)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (cofibrantHammockVertex A Y))).map α.op
      (cofibrantSourceRoofProductCommaNativeSliceSimplex A X Y b Γ t) =
    cofibrantSourceRoofProductCommaNativeSliceSimplex A X Y b
      (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom) := by
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map α) (𝟙 Δ[0]) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (cofibrantSourceRoofProductCommaNativeSimplex A X Y b Γ t)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (cofibrantAlgebraRelativeCategory A)) _⦋m + 1⦌ =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom ≫ SSet.yonedaEquiv.symm z)
    (cofibrantSourceRoofProductCommaNativeSimplex_naturality A X Y b Γ t α)

def cofibrantSourceRoofProductCommaNativePrism :
    (Δ[1] : SSet.{u + 1}) ⊗ nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (cofibrantHammockVertex A Y)) where
  app _ := ↾fun a => cofibrantSourceRoofProductCommaNativeSliceSimplex A X Y b a.2
    (stdSimplex.objEquiv a.1).toOrderHom
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro a
    exact (cofibrantSourceRoofProductCommaNativeSliceSimplex_naturality A X Y b a.2
      (stdSimplex.objEquiv a.1).toOrderHom α.unop).symm

lemma cofibrantSourceRoofProductCommaNativePrism_app {n : ℕ}
    (Γ : (nerve (cofibrantSourceRoofProductComma A X Y b)) _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (cofibrantSourceRoofProductCommaNativePrism A X Y b).app (Opposite.op ⦋n⦌) (t, Γ) =
      cofibrantSourceRoofProductCommaNativeSliceSimplex A X Y b Γ
        (stdSimplex.objEquiv t).toOrderHom := rfl

end SerrePositivity.EInfinity.BarrattEccles
