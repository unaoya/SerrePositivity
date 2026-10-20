module

public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyConstantFamily

/-!
概要：指定ホモトピーの自然性を、任意の区間写像空間の族で表す。
方針：族と指定円柱から関手単体集合内の正方形を作り、四辺と合成を照合する。
規約：元の標準の前後合成を保持。使われ方：Quillen 導来単位の標準比較の可換性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A X Y : SSet.{u}} {U V : X ⟶ Y}
  (H : SSet.Homotopy U V) {x y : X _⦋0⦌}
  (f : A ⟶ intervalMappingSpace x y)
/-- 元のホモトピーと任意の区間族から、関手単体集合内の正方形を作る。 -/
def homotopyFamilySquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj Y :=
  curry ((α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
    ((intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) ≫ H.h)
/-- 正方形の下辺は、元の始点関手による区間族の像である。 -/
lemma homotopyFamilySquare_bottom : SSet.ι₀ ≫ homotopyFamilySquare H f =
    curry (intervalFamilyHomotopy (f ≫ intervalFunctorMap U x y)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left, homotopyFamilySquare, uncurry_curry, uncurry_curry]
  have he : (A ◁ SSet.ι₀) ≫ (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
      ((intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) =
        (intervalFamilyHomotopy f).h ≫ SSet.ι₀ := by rfl
  change ((A ◁ SSet.ι₀) ≫
    (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
    ((intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
  rw [he, Category.assoc, H.h₀]
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry f ≫ U = _
  rw [← intervalFunctorMap_uncurry]
  rfl
/-- 正方形の上辺は、元の終点関手による区間族の像である。 -/
lemma homotopyFamilySquare_top : SSet.ι₁ ≫ homotopyFamilySquare H f =
    curry (intervalFamilyHomotopy (f ≫ intervalFunctorMap V x y)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left, homotopyFamilySquare, uncurry_curry, uncurry_curry]
  have he : (A ◁ SSet.ι₁) ≫ (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
      ((intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) =
        (intervalFamilyHomotopy f).h ≫ SSet.ι₁ := by rfl
  change ((A ◁ SSet.ι₁) ≫
    (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
    ((intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
  rw [he, Category.assoc, H.h₁]
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry f ≫ V = _
  rw [← intervalFunctorMap_uncurry]
  rfl
/-- 二つの側辺は、元の両端点での指定ホモトピーの制限である。 -/
lemma homotopyFamilySquare_side (i : Fin 2) : prismEndpoint i _ ≫ homotopyFamilySquare H f =
    curry (functorHomotopyPrecomp H
      (SSet.const (if i = 0 then x else y) : A ⟶ X)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left, homotopyFamilySquare, uncurry_curry, uncurry_curry]
  fin_cases i
  · have he : (A ◁ prismEndpoint 0 (Δ[1] : SSet.{u})) ≫
        (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
        ((intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) =
          ((SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ≫ (intervalFamilyHomotopy f).h) ▷ Δ[1] := by rfl
    change ((A ◁ prismEndpoint 0 (Δ[1] : SSet.{u})) ≫
      (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
      ((intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
    rw [he, (intervalFamilyHomotopy f).h₀]
    rfl
  · have he : (A ◁ prismEndpoint 1 (Δ[1] : SSet.{u})) ≫
        (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
        ((intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) =
          ((SSet.ι₁ : A ⟶ A ⊗ Δ[1]) ≫ (intervalFamilyHomotopy f).h) ▷ Δ[1] := by rfl
    change ((A ◁ prismEndpoint 1 (Δ[1] : SSet.{u})) ≫
      (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
      ((intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
    rw [he, (intervalFamilyHomotopy f).h₁]
    rfl
/-- 任意の区間族上で、指定ホモトピーの自然性の合成式が成り立つ。 -/
lemma homotopyFamily_composition [Quasicategory Y] :
    intervalFamilyHom (f ≫ intervalFunctorMap U x y) ≫
      constantFunctorHomMap A (functorHomEvaluate
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) y) =
    constantFunctorHomMap A (functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) x) ≫
      intervalFamilyHom (f ≫ intervalFunctorMap V x y) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have hq := homMk_comp_eq_of_square
    (intervalFamilyEdge (f ≫ intervalFunctorMap U x y))
    (intervalFamilyEdge (f ≫ intervalFunctorMap V x y))
    (functorEdgeOfSimplicialHomotopy (homotopyConstantFamily (A := A) H x))
    (functorEdgeOfSimplicialHomotopy (homotopyConstantFamily (A := A) H y))
    (homotopyFamilySquare H f) ?_ ?_ ?_ ?_
  · rw [homotopyConstantFamily_hom, homotopyConstantFamily_hom] at hq
    exact hq
  · change (homotopyFamilySquare H f).app (Opposite.op ⦋1⦌)
      (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₀ ≫ homotopyFamilySquare H f) = _
    exact congrArg SSet.yonedaEquiv (homotopyFamilySquare_bottom H f)
  · change (homotopyFamilySquare H f).app (Opposite.op ⦋1⦌)
      (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₁ ≫ homotopyFamilySquare H f) = _
    exact congrArg SSet.yonedaEquiv (homotopyFamilySquare_top H f)
  · change (homotopyFamilySquare H f).app (Opposite.op ⦋1⦌)
      (_, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ homotopyFamilySquare H f) = _
    exact congrArg SSet.yonedaEquiv (homotopyFamilySquare_side H f 0)
  · change (homotopyFamilySquare H f).app (Opposite.op ⦋1⦌)
      (_, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ homotopyFamilySquare H f) = _
    exact congrArg SSet.yonedaEquiv (homotopyFamilySquare_side H f 1)

/-- 指定ホモトピーの自然性は、標準の前後合成を結ぶ単体的ホモトピーを与える。 -/
lemma intervalFunctorMap_homotopy_naturality [Quasicategory Y] :
    Nonempty (SSet.Homotopy
      (intervalFunctorMap U x y ≫ intervalPostcompose (U.app (Opposite.op ⦋0⦌) x)
        (functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
          (functorEdgeOfSimplicialHomotopy H)) y))
      (intervalFunctorMap V x y ≫ intervalPrecompose (V.app (Opposite.op ⦋0⦌) y)
        (functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
          (functorEdgeOfSimplicialHomotopy H)) x))) := by
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalPostcompose_family, intervalPrecompose_family]
  simpa only [Category.id_comp] using homotopyFamily_composition H
    (𝟙 (intervalMappingSpace x y))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
