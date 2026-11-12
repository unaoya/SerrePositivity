module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareClass

/-!
概要：四辺が任意の正方形の二つの合成をホモトピー圏で比較する。
方針：二つの三角形が同じ対角辺を表すことを用いる。
規約：単体集合の quasicategory 性は不要。
使われ方：comma の正方形から単位と標的の合成関係を得る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：正方形の下辺・右辺の合成と左辺・上辺の合成は h で等しい。
方針：二つの三角形の対角辺を共通に取る。
規約：端点を含め四辺を指定する。
使われ方：単位比較の導来 fiber への射のホモトピー条件。 -/
lemma homMk_comp_eq_of_square {Z : SSet.{u}} {x₀ x₁ y₀ y₁ : Z _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj Z) x₀ x₁)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj Z) y₀ y₁)
    (l : SSet.Truncated.Edge (X := (truncation 2).obj Z) x₀ y₀)
    (r : SSet.Truncated.Edge (X := (truncation 2).obj Z) x₁ y₁)
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
        l.edge)
    (hr : (((SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 1)).tensor
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q)).edge =
        r.edge) :
    SSet.Truncated.HomotopyCategory.homMk f ≫ SSet.Truncated.HomotopyCategory.homMk r =
      SSet.Truncated.HomotopyCategory.homMk l ≫ SSet.Truncated.HomotopyCategory.homMk g := by
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
    (stdSimplex.obj₀Equiv.symm 0))).map ((truncation 2).map Q)
  let er := ((SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 1)).tensor
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q)
  let d := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q)
  have hx : Q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) = x₀ :=
    b.src_eq.symm.trans ((congrArg (Z.map (SimplexCategory.δ (1 : Fin 2)).op) hb).trans f.src_eq)
  have hy : Q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) = y₁ :=
    er.tgt_eq.symm.trans ((congrArg (Z.map (SimplexCategory.δ (0 : Fin 2)).op) hr).trans
      r.tgt_eq)
  let diag : SSet.Truncated.Edge (X := (truncation 2).obj Z) x₀ y₁ :=
    ⟨d.edge, d.src_eq.trans hx, d.tgt_eq.trans hy⟩
  let t₀ := ((SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
    (SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map Q)
  let t₁ := ((SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
    (SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map Q)
  have s₀ : SSet.Truncated.Edge.CompStruct f r diag := {
    simplex := t₀.simplex
    d₂ := t₀.d₂.trans hb
    d₀ := t₀.d₀.trans hr
    d₁ := t₀.d₁ }
  have s₁ : SSet.Truncated.Edge.CompStruct l g diag := {
    simplex := t₁.simplex
    d₂ := t₁.d₂.trans hl
    d₀ := t₁.d₀.trans ht
    d₁ := t₁.d₁ }
  have h₀ := SSet.Truncated.HomotopyCategory.homMk_comp_homMk s₀
  have h₁ := SSet.Truncated.HomotopyCategory.homMk_comp_homMk s₁
  exact h₀.trans h₁.symm


end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
