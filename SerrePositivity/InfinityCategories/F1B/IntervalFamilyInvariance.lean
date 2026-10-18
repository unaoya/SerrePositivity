module

public import SerrePositivity.InfinityCategories.F1B.IntervalFamilySquare
public import SerrePositivity.InfinityCategories.F1B.RightHomotopySquare

/-!
概要：区間写像空間の族が表す h Fun の射はホモトピーに不変。
方針：ホモトピーを正方形へ展開し、固定された両端の恒等辺を相殺する。
規約：不変性自体には quasicategory 性は不要。
使われ方：パラメータ付き写像空間のホモトピー類による Hom の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：族のホモトピーは同じ h Fun の射を与える。
方針：二重区間の四辺の計算と正方形の合成関係を使う。
規約：A,X は任意の単体集合。
使われ方：族の表示をホモトピー類へ降ろす。 -/
lemma intervalFamilyHom_eq_of_homotopy {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    intervalFamilyHom f = intervalFamilyHom g := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  apply homMk_eq_of_square (intervalFamilyEdge f) (intervalFamilyEdge g) (intervalFamilySquare H)
  · change (intervalFamilySquare H).app (Opposite.op ⦋1⦌)
        (homotopyIntervalEdge.edge, (SSet.Truncated.Edge.id
          (X := (truncation 2).obj (Δ[1] : SSet.{u}))
            (stdSimplex.obj₀Equiv.symm 0)).edge) = _
    rw [← hi]
    exact congrArg SSet.yonedaEquiv (intervalFamilySquare_zero H)
  · change (intervalFamilySquare H).app (Opposite.op ⦋1⦌)
        (homotopyIntervalEdge.edge, (SSet.Truncated.Edge.id
          (X := (truncation 2).obj (Δ[1] : SSet.{u}))
            (stdSimplex.obj₀Equiv.symm 1)).edge) = _
    rw [← hi]
    exact congrArg SSet.yonedaEquiv (intervalFamilySquare_one H)
  · change (intervalFamilySquare H).app (Opposite.op ⦋1⦌)
        ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
          (stdSimplex.obj₀Equiv.symm 0)).edge, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ intervalFamilySquare H) = _
    rw [intervalFamilySquare_source]
    exact pinchedConstant_one (X := (ihom A).obj X)
      (functorVertex (SSet.const x : A ⟶ X))
  · change (intervalFamilySquare H).app (Opposite.op ⦋1⦌)
        ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
          (stdSimplex.obj₀Equiv.symm 1)).edge, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ intervalFamilySquare H) = _
    rw [intervalFamilySquare_target]
    exact pinchedConstant_one (X := (ihom A).obj X)
      (functorVertex (SSet.const y : A ⟶ X))

/-- 概要：h Fun の射の等式と族の間の実際のホモトピーの存在は同値。
方針：正方形による不変性と右ホモトピーの三角形による回収を合わせる。
規約：標的 X は quasicategory、パラメータ A は任意。
使われ方：ホモトピー類による定値関手間の Hom の表示。 -/
lemma intervalFamilyHom_eq_iff_homotopy {A X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f g : A ⟶ intervalMappingSpace x y} :
    intervalFamilyHom f = intervalFamilyHom g ↔ Nonempty (SSet.Homotopy f g) :=
  ⟨intervalFamilyHom_eq_imp_homotopy, fun ⟨H⟩ ↦ intervalFamilyHom_eq_of_homotopy H⟩

end SerrePositivity.InfinityCategories
