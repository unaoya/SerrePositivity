module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameters

/-!
概要：両側の辺が退化する正方形は二つの横辺の同じホモトピー圏の射を与える。
方針：正方形の二つの三角形の合成関係を同じ対角辺で比較する。
規約：標的の quasicategory 性は不要。
使われ方：区間写像空間のパラメータ族のホモトピー不変性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：縦辺が恒等辺の正方形の横辺は h で等しい。
方針：下・右の三角形と左・上の三角形を共通の対角辺で比較する。
規約：四辺の条件は一次単体の等式で受け取る。
使われ方：辺の端点の輸送を含めずに相対ホモトピーの類を比較する。 -/
lemma homMk_eq_of_square {Z : SSet.{u}} {x y : Z _⦋0⦌}
    (f g : SSet.Truncated.Edge (X := (truncation 2).obj Z) x y)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z)
    (hb : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 0))).map ((truncation 2).map Q)).edge = f.edge)
    (ht : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 1))).map ((truncation 2).map Q)).edge = g.edge)
    (hl : (((SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 0)).tensor
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q)).edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj Z) x).edge)
    (hr : (((SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 1)).tensor
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q)).edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj Z) y).edge) :
    SSet.Truncated.HomotopyCategory.homMk f = SSet.Truncated.HomotopyCategory.homMk g := by
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
    (stdSimplex.obj₀Equiv.symm 0))).map ((truncation 2).map Q)
  let r := ((SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 1)).tensor
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q)
  let d := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q)
  have hx : Q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) = x :=
    b.src_eq.symm.trans ((congrArg (Z.map (SimplexCategory.δ (1 : Fin 2)).op) hb).trans f.src_eq)
  have hy : Q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) = y :=
    r.tgt_eq.symm.trans ((congrArg (Z.map (SimplexCategory.δ (0 : Fin 2)).op) hr).trans
      (SSet.Truncated.Edge.id (X := (truncation 2).obj Z) y).tgt_eq)
  let diag : SSet.Truncated.Edge (X := (truncation 2).obj Z) x y :=
    ⟨d.edge, d.src_eq.trans hx, d.tgt_eq.trans hy⟩
  let t₀ := ((SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
    (SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map Q)
  let t₁ := ((SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
    (SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map Q)
  have s₀ : SSet.Truncated.Edge.CompStruct f
      (SSet.Truncated.Edge.id (X := (truncation 2).obj Z) y) diag := {
    simplex := t₀.simplex
    d₂ := t₀.d₂.trans hb
    d₀ := t₀.d₀.trans hr
    d₁ := t₀.d₁ }
  have s₁ : SSet.Truncated.Edge.CompStruct
      (SSet.Truncated.Edge.id (X := (truncation 2).obj Z) x) g diag := {
    simplex := t₁.simplex
    d₂ := t₁.d₂.trans hl
    d₀ := t₁.d₀.trans ht
    d₁ := t₁.d₁ }
  have h₀ := SSet.Truncated.HomotopyCategory.homMk_comp_homMk s₀
  have h₁ := SSet.Truncated.HomotopyCategory.homMk_comp_homMk s₁
  simpa using h₀.trans h₁.symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
