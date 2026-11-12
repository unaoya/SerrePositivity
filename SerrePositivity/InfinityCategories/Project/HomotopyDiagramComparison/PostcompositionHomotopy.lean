module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorHomUncurry

/-!
概要：元の指定ホモトピーと標準単位を、任意の関手単体集合への後合成に移す。
方針：同じ標準単位の式と、直積パラメータ上の Hom 全単射を照合する。
規約：添字の quasicategory 性を仮定しない。使われ方：一般 coherent 極限の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 元の指定ホモトピーを、任意のパラメータ上の後合成のホモトピーに移す。 -/
def postcompositionHomotopy {X Y : SSet.{u}} {U V : X ⟶ Y}
    (H : SSet.Homotopy U V) (K : SSet.{u}) :
    SSet.Homotopy ((ihom K).map U) ((ihom K).map V) where
  h := curry ((α_ K ((ihom K).obj X) (Δ[1] : SSet.{u})).inv ≫
    ((ihom.ev K).app X ▷ (Δ[1] : SSet.{u})) ≫ H.h)
  h₀ := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    have he : (K ◁ SSet.ι₀) ≫ (α_ K ((ihom K).obj X) (Δ[1] : SSet.{u})).inv ≫
        ((ihom.ev K).app X ▷ (Δ[1] : SSet.{u})) =
          (ihom.ev K).app X ≫ SSet.ι₀ := by rfl
    change ((K ◁ SSet.ι₀) ≫ (α_ K ((ihom K).obj X) (Δ[1] : SSet.{u})).inv ≫
      ((ihom.ev K).app X ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
    rw [he, Category.assoc, H.h₀]
    rfl
  h₁ := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    have he : (K ◁ SSet.ι₁) ≫ (α_ K ((ihom K).obj X) (Δ[1] : SSet.{u})).inv ≫
        ((ihom.ev K).app X ▷ (Δ[1] : SSet.{u})) =
          (ihom.ev K).app X ≫ SSet.ι₁ := by rfl
    change ((K ◁ SSet.ι₁) ≫ (α_ K ((ihom K).obj X) (Δ[1] : SSet.{u})).inv ≫
      ((ihom.ev K).app X ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
    rw [he, Category.assoc, H.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 元の標準単位のホモトピーから、後合成関手の標準単位候補を作る。 -/
def postcompositionUnitHomotopy {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (𝟙 X) (F ≫ G)) (K : SSet.{u}) :
    SSet.Homotopy (𝟙 ((ihom K).obj X)) ((ihom K).map F ≫ (ihom K).map G) where
  h := (postcompositionHomotopy H K).h
  h₀ := by
    change SSet.ι₀ ≫ (postcompositionHomotopy H K).h = 𝟙 _
    simpa only [CategoryTheory.Functor.map_id] using (postcompositionHomotopy H K).h₀
  h₁ := by
    change SSet.ι₁ ≫ (postcompositionHomotopy H K).h = (ihom K).map F ≫ (ihom K).map G
    simpa only [CategoryTheory.Functor.map_comp] using (postcompositionHomotopy H K).h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 後合成の同じ単位成分を uncurry すると、元の単位の制限になる。 -/
lemma functorHomUncurry_unit_precomp {K A X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (𝟙 X) (F ≫ G)) (U : A ⟶ (ihom K).obj X) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry (K := K) (A := A) (X := X)
      (U := U) (V := U ≫ (ihom K).map F ≫ (ihom K).map G)
      ((hoFunctor.map ((pre U).app ((ihom K).obj X))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (postcompositionUnitHomotopy H K)))) =
    (hoFunctor.map ((pre (uncurry U)).app X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
