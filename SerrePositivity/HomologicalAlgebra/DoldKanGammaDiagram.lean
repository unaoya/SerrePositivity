module
public import SerrePositivity.HomologicalAlgebra.FunctorComplexExchange
public import SerrePositivity.HomologicalAlgebra.DoldKanGammaMapNaturality
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
概要：図式圏で Γ を取る関手と、各対象で Γ を取る関手の指定自然同型。
方針：評価関手の余積比較を用い、元の図式射と鎖射への両自然性で組み立てる。
規約：図式の全対象・全射と単体方向の全作用素を保つ。
使われ方：HA 1.2.4、G10 の図式圏の Dold–Kan から対象ごとの Hom 空間への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type u) [Category.{v} J]
variable (C : Type u') [Category.{v'} C] [Abelian C]

/-- 図式圏で Γ を取り、単体方向と添字方向を交換する全関手。 -/
def diagramGammaFunctor : ChainComplex (J ⥤ C) ℕ ⥤ J ⥤ SimplicialObject C :=
  (Abelian.DoldKan.Γ : ChainComplex (J ⥤ C) ℕ ⥤ SimplicialObject (J ⥤ C)) ⋙
    flipFunctor SimplexCategoryᵒᵖ J C

/-- 各図式対象で鎖複体を評価し、そのまま Γ を適用する全関手。 -/
def pointwiseGammaFunctor : ChainComplex (J ⥤ C) ℕ ⥤ J ⥤ SimplicialObject C :=
  complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight J (ChainComplex C ℕ) (SimplicialObject C)).obj Abelian.DoldKan.Γ

/-- 指定余積比較による、図式圏の Γ と対象ごとの Γ の全自然同型。 -/
def pointwiseGammaIso : pointwiseGammaFunctor J C ≅ diagramGammaFunctor J C :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun j => gammaMapIso ((evaluation J C).obj j) K)
      (fun f => gammaMapIso_functor_naturality ((evaluation J C).map f) K))
    (by
      intro K L f
      apply NatTrans.ext
      funext j
      exact gammaMapIso_naturality ((evaluation J C).obj j) f)

end SerrePositivity.HomologicalAlgebra
