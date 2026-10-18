module
public import SerrePositivity.InfinityCategories.Core.JoinBoundary
public import SerrePositivity.InfinityCategories.Core.RelativeTerminalExtension

/-! # 右端を固定した join の境界持ち上げ

概要：相対終点境界充填を、境界と点の pushout-join の表示へ移す。
方針：標準単体とその境界の join 同型で持ち上げ問題を運ぶ。
規約：右因子の頂点を相対終点として固定する。
使われ方：S4 の指定終点への写像空間の充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対終点境界充填は境界と点の join の境界も持ち上げる。
方針：境界の最後の頂点と join の右因子の一致を使って標準形へ移送する。
規約：右因子の部分複体は空境界に等しいものを許す。
使われ方：指定した終点への右写像空間の境界充填。 -/
lemma TerminalBoundaryLifting.exists_joinBoundary_lift {E B : SSet.{u}}
    {p : E ⟶ B} {y : E _⦋0⦌} (hy : TerminalBoundaryLifting p y)
    (n : ℕ) (B₀ : (Δ[0] : SSet.{u}).Subcomplex) (hB₀ : B₀ = boundary 0)
    (a : (joinUnion (boundary n) B₀ : SSet.{u}) ⟶ E)
    (b : join (Δ[n] : SSet.{u}) Δ[0] ⟶ B)
    (hw : a ≫ p = (joinUnion (boundary n) B₀).ι ≫ b)
    (hlast : joinInr (boundary n : SSet.{u}) Δ[0] ≫
      joinUnionLeft (boundary n) B₀ ≫ a = SSet.yonedaEquiv.symm y) :
    ∃ F : join (Δ[n] : SSet.{u}) Δ[0] ⟶ E,
      (joinUnion (boundary n) B₀).ι ≫ F = a ∧ F ≫ p = b := by
  subst B₀
  let ep : Arrow.mk (joinUnion (boundary n) (boundary 0)).ι ≅
      Arrow.mk (boundary (n + 1)).ι :=
    Arrow.isoMk (boundaryJoinIso n 0) (joinStdSimplexIso n 0) (boundaryJoinIso_hom_ι n 0)
  have hi : (boundaryJoinIso n 0).inv ≫ (joinUnion (boundary n) (boundary 0)).ι =
      (boundary (n + 1)).ι ≫ (joinStdSimplexIso n 0).inv := ep.inv.w
  let a' := (boundaryJoinIso n 0).inv ≫ a
  let b' := (joinStdSimplexIso n 0).inv ≫ b
  have hv : boundaryVertex n (Fin.last (n + 1)) ≫ a' = SSet.yonedaEquiv.symm y := by
    dsimp only [a']
    rw [← boundaryJoinIso_inr_vertex]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact hlast
  have sq : CommSq a' (boundary (n + 1)).ι p b' := by
    constructor
    dsimp only [a', b']
    rw [Category.assoc, hw, ← Category.assoc, hi, Category.assoc]
  obtain ⟨F, hF, hFp⟩ := hy n a' b' hv sq
  refine ⟨(joinStdSimplexIso n 0).hom ≫ F, ?_, ?_⟩
  · rw [← Category.assoc, ← boundaryJoinIso_hom_ι, Category.assoc, hF]
    exact (boundaryJoinIso n 0).hom_inv_id_assoc a
  · rw [Category.assoc, hFp]
    exact (joinStdSimplexIso n 0).hom_inv_id_assoc b

end SerrePositivity.InfinityCategories
