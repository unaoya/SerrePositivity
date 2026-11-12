module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalComposition

/-!
概要：区間写像空間の三つの全族を、同じ実三角形の面として h Fun の合成へ移す。
方針：三角形の族を curry して関手単体集合の二単体を作り、元の三面を保つ。
規約：パラメータに quasicategory 性を課さない。
使われ方：G8 の共通の錐 span の射と標準後合成の全族の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：実三角形の族の三面が指定された区間族なら、その同じ二単体は合成構造を与える。
方針：全族を curry し、Yoneda の自然性で三面を照合する。
規約：三角形と面の等式をデータとして保持。使われ方：h Fun の全パラメータ合成。 -/
def intervalTriangleFamilyCompStruct {A X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) (g : A ⟶ intervalMappingSpace y z)
    (h : A ⟶ intervalMappingSpace x z) (T : A ⊗ (Δ[2] : SSet.{u}) ⟶ X)
    (h01 : (A ◁ stdSimplex.δ (2 : Fin 3)) ≫ T = (intervalFamilyHomotopy f).h)
    (h12 : (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ T = (intervalFamilyHomotopy g).h)
    (h02 : (A ◁ stdSimplex.δ (1 : Fin 3)) ≫ T = (intervalFamilyHomotopy h).h) :
    SSet.Truncated.Edge.CompStruct (intervalFamilyEdge f) (intervalFamilyEdge g)
      (intervalFamilyEdge h) where
  simplex := SSet.yonedaEquiv (curry T)
  d₂ := by
    change ((ihom A).obj X).map (SimplexCategory.δ (2 : Fin 3)).op
      (SSet.yonedaEquiv (curry T)) = _
    change (A ◁ stdSimplex.map (SimplexCategory.δ (2 : Fin 3))) ≫ T =
      (intervalFamilyHomotopy f).h at h01
    rw [SSet.yonedaEquiv_naturality, ← curry_natural_left, h01]
    rfl
  d₀ := by
    change ((ihom A).obj X).map (SimplexCategory.δ (0 : Fin 3)).op
      (SSet.yonedaEquiv (curry T)) = _
    change (A ◁ stdSimplex.map (SimplexCategory.δ (0 : Fin 3))) ≫ T =
      (intervalFamilyHomotopy g).h at h12
    rw [SSet.yonedaEquiv_naturality, ← curry_natural_left, h12]
    rfl
  d₁ := by
    change ((ihom A).obj X).map (SimplexCategory.δ (1 : Fin 3)).op
      (SSet.yonedaEquiv (curry T)) = _
    change (A ◁ stdSimplex.map (SimplexCategory.δ (1 : Fin 3))) ≫ T =
      (intervalFamilyHomotopy h).h at h02
    rw [SSet.yonedaEquiv_naturality, ← curry_natural_left, h02]
    rfl

/-- 概要：実三角形の族は、同じ三つの全族の h Fun における合成則を与える。
方針：構成した同じ二単体の合成関係をホモトピー圏へ送る。
規約：各頂点の等式への弱化はしない。使われ方：標準の後合成との照合。 -/
lemma intervalTriangleFamily_hom_comp {A X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) (g : A ⟶ intervalMappingSpace y z)
    (h : A ⟶ intervalMappingSpace x z) (T : A ⊗ (Δ[2] : SSet.{u}) ⟶ X)
    (h01 : (A ◁ stdSimplex.δ (2 : Fin 3)) ≫ T = (intervalFamilyHomotopy f).h)
    (h12 : (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ T = (intervalFamilyHomotopy g).h)
    (h02 : (A ◁ stdSimplex.δ (1 : Fin 3)) ≫ T = (intervalFamilyHomotopy h).h) :
    intervalFamilyHom f ≫ intervalFamilyHom g = intervalFamilyHom h :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (intervalTriangleFamilyCompStruct f g h T h01 h12 h02)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
