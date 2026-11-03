module
public import SerrePositivity.InfinityCategories.Stable.ZeroReturnPasting
public import SerrePositivity.InfinityCategories.Stable.TerminalCompositeTriangle
public import SerrePositivity.InfinityCategories.F1.SquareTranspose

/-! # 零終点を付加する押し出し長方形

概要：下側の最後の頂点が零である合成二単体を、指定押し出しの右に付加する。
方針：外側 span の第一枝が零へ向かうことから余極限の存在を得て貼り合わせる。
規約：元の押し出しと下側二単体を保持。使われ方：任意の押し出しの引き戻し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：第一枝が終対象へ向かう指定 span は余極限を持つ。
方針：二枝を交換して既存の第二枝での判定を使う。
規約：安定性から余極限の存在を得る。使われ方：零終点を持つ外側 span。 -/
lemma hasColimit_span_of_terminal_first {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X)
    (hz : IsTerminalVertex ((horn₂₀.ι₀₁ ≫ p).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : HasColimit p := by
  apply (hasColimit_iff_restrict_of_precompositionEquivalence p spanSwapIso.hom
    (isPrecompositionEquivalence_of_iso spanSwapIso)).2
  apply hasColimit_span_of_terminal_second
  rw [← Category.assoc, show spanSwapIso.hom = spanSwap from rfl, spanSwap_right]
  exact hz

/-- 概要：零終点を持つ底辺二単体を指定押し出しに付加し、両側押し出しの長方形を作る。
方針：外側 span の零へ向かう第一枝で余極限を作り、五頂点図式から延長する。
規約：左四角形と底辺二単体を厳密に保持。使われ方：安定性の任意の四角形への拡張。 -/
lemma exists_pushoutRectangle_of_zeroEnd {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : IsPushoutSquare L)
    (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ)
    (hz : IsZeroVertex (τ.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      pastingSquare F 2 = L ∧ pastingBottomTriangle F = τ ∧
        IsPushoutSquare (pastingSquare F 0) ∧ IsPushoutSquare (pastingSquare F 1) := by
  let G := pastingCornerGlue L τ h
  let p := pastingOuterBaseToCorner ≫ G
  let k := pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι
  have := pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  have hp : HasColimit p := by
    apply (hasColimit_iff_of_trivialRestriction p k).2
    apply hasColimit_span_of_terminal_first
    have he : horn₂₀.ι₀₁ ≫ (k ≫ p) = stdSimplex.δ (1 : Fin 3) ≫ τ := by
      change horn₂₀.ι₀₁ ≫ ((pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι) ≫
        (pastingOuterBaseToCorner ≫ G)) = _
      calc
        _ = (horn₂₀.ι₀₁ ≫ (pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι ≫
            pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
        _ = _ := by
          rw [pastingOuterStandardSpan_bottomEdge, Category.assoc, pastingCornerGlue_bottom]
    rw [he]
    exact hz.2
  obtain ⟨d, hd⟩ := hp
  obtain ⟨F, hleft, hbottom, hright, _⟩ :=
    exists_pushoutRectangle_of_left_and_bottom L τ h hL d hd
  refine ⟨F, hleft, hbottom, hright, ?_⟩
  apply isPushoutSquare_pasting F _ hright
  rw [hleft]
  exact hL

end SerrePositivity.InfinityCategories
