module

public import SerrePositivity.KST.LocalizingInvariants.VerdierArrowLifting
public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexRefinementCocone

/-!
概要：元の商の次辺を実右分数で表し、前段全体の精密化と同じ合成二単体へ接続する。
方針：Verdier の実辺分数に厳密終端精密化を適用し、同じ分子の余錐を構成する。
規約：全次数（零次を含む）、元の商辺、分母成分、分子の全一次単体を保持する。
使われ方：c5 の帰納的持ち上げで、次辺と前段比較の共有経路を構成する実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 実右分数・全前段への分母・元の分子の余錐を、同じ指定合成二単体付きで構成する。 -/
lemma exists_verdierSimplexSuccessorRoof {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) (z : B.obj _⦋0⦌)
    (f : Truncated.Edge (X := (truncation 2).obj C.obj)
      (q.hom.app (Opposite.op ⦋0⦌)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
      (q.hom.app (Opposite.op ⦋0⦌) z)) :
    ∃ (y : B.obj _⦋0⦌)
      (s : Truncated.Edge (X := (truncation 2).obj B.obj) y
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
      (g : Truncated.Edge (X := (truncation 2).obj B.obj) y z)
      (D' : (Δ[n] : SSet.{u}) ⟶ B.obj)
      (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (functorVertex D') (functorVertex D)) (c : JoinCocone D'),
      s.edge ∈ weakEquivalences i ∧
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      D'.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) = y ∧
      (evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (Fin.last n))).app
        (Opposite.op ⦋1⦌) t.edge = s.edge ∧
      c.vertex = z ∧
      (joinStdSimplexIso 0 0).inv ≫
        joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ c.val = SSet.yonedaEquiv.symm g.edge ∧
      Nonempty (Truncated.Edge.CompStruct
        (s.map ((truncation 2).map q.hom)) f (g.map ((truncation 2).map q.hom))) := by
  obtain ⟨y, s, g, hs, hcomp⟩ := verdierProjection_edge_fraction h f
  obtain ⟨D', t, ht, hv, hlast⟩ := exists_verdierSimplexTerminalRefinementMap h D s hs
  have hpoint : SSet.yonedaEquiv (simplexLastPoint n ≫ D') = y := by
    rw [SSet.yonedaEquiv_comp, simplexLastPoint, Equiv.apply_symm_apply]
    exact hv
  let g' := (SSet.Edge.ofTruncated (X := B.obj) g).ofEq hpoint.symm rfl
  obtain ⟨c, hc, hedge⟩ := exists_simplexCocone_of_last_edge D' g'.toTruncated
  exact ⟨y, s, g, D', t, c, hs, ht, hv, hlast, hc, hedge, hcomp⟩

end SerrePositivity.KST.LocalizingInvariants
