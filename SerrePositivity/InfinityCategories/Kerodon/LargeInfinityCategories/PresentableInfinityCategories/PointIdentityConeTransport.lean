module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackSliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：任意の点射の恒等錐と、その固定図式移送・後合成・引き戻し比較を揃える。
方針：元の点射の Yoneda 頂点への全定値射を使う。
規約：固定点射を元の射のまま保持する。
使われ方：compact 始域の可算回収を元の fiber 内の射へ厳密化する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の点射そのものの恒等錐。
方針：点の Yoneda 頂点への定値射を取る。
規約：固定図式を正規化した別の点射に変えない。
使われ方：元の対象上の恒等射の比較。 -/
def pointIdentityCone {C : SSet.{u}} (r : (Δ[0] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver r) _⦋0⦌ :=
  ⟨SSet.const (SSet.yonedaEquiv r), by
    rw [SSet.comp_const, ← SSet.yonedaEquiv_symm_zero, Equiv.symm_apply_apply]⟩

/-- 概要：Yoneda 表示された点の恒等錐は既存の頂点恒等錐そのもの。
方針：元の頂点を Yoneda の逆関係で回収する。
規約：slice の実頂点の等式。
使われ方：交互構成の恒等錐との比較。 -/
lemma pointIdentityCone_yoneda {C : SSet.{u}} (x : C _⦋0⦌) :
    pointIdentityCone (SSet.yonedaEquiv.symm x) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone x := by
  apply Subtype.ext
  change SSet.const (SSet.yonedaEquiv (SSet.yonedaEquiv.symm x)) = SSet.const x
  rw [Equiv.apply_symm_apply]

/-- 概要：点射の等式による移送は元の恒等錐を保つ。
方針：点射の等式で置換して恒等移送へ戻す。
規約：元の slice の実頂点を移送する。
使われ方：像の標的点と元の fiber の標的点を揃える。 -/
lemma pointIdentityCone_eqToHom {C : SSet.{u}} {r s : (Δ[0] : SSet.{u}) ⟶ C}
    (h : r = s) :
    (eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver h)).app (Opposite.op ⦋0⦌) (pointIdentityCone r) =
      pointIdentityCone s := by
  cases h
  rfl

/-- 概要：点射の恒等錐の後合成は元の後合成点射の恒等錐。
方針：定値射の後合成と Yoneda の自然性を使う。
規約：slice の実頂点の等式。
使われ方：第一成分の像の恒等錐を元の底上で比較する。 -/
lemma pointIdentityCone_postcomp {E B : SSet.{u}} (r : (Δ[0] : SSet.{u}) ⟶ E)
    (p : E ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp r p).app (Opposite.op ⦋0⦌) (pointIdentityCone r) =
      pointIdentityCone (r ≫ p) := by
  apply Subtype.ext
  change SSet.const (SSet.yonedaEquiv r) ≫ p = SSet.const (SSet.yonedaEquiv (r ≫ p))
  rw [SSet.const_comp, SSet.yonedaEquiv_comp]

/-- 概要：元の引き戻しの第二成分の恒等錐の像は、共通の第一成分像の恒等錐。
方針：元の引き戻しの可換式と定値射の後合成を使う。
規約：点射・大域単位の選び直しを要求しない。
使われ方：compact fiber 射の回収の第二成分。 -/
lemma pullbackSliceBaseMap_pointIdentityCone {E D B : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) (x : (Δ[0] : SSet.{u}) ⟶ pullback p q) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSliceBaseMap p q x).app (Opposite.op ⦋0⦌)
      (pointIdentityCone (x ≫ pullback.snd p q)) =
        pointIdentityCone ((x ≫ pullback.fst p q) ≫ p) := by
  apply Subtype.ext
  change SSet.const (SSet.yonedaEquiv (x ≫ pullback.snd p q)) ≫ q =
    SSet.const (SSet.yonedaEquiv ((x ≫ pullback.fst p q) ≫ p))
  rw [SSet.const_comp, ← SSet.yonedaEquiv_comp]
  congr 1
  simp only [Category.assoc, pullback.condition]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
