module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomTargetNaturality

/-!
# 同じ smart 切断からの実 Dold–Kan 関手

概要：元の複体を非正 smart 切断・次数反転・実 Γ・台単体集合へ送る。
方針：元の三つの実関手を合成する。
規約：零次数は cycles のままで、ホモロジーの商に置き換えない。
使われ方：正規化テンソル Hom 比較の全二変数自然性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def truncatedDoldKanFunctor : Complex A ⥤ SSet.{u} :=
  (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat.{u} A) ⋙
    (Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat A) (Type u)).obj (forget (ModuleCat A))

end SerrePositivity.ComplexLimits
