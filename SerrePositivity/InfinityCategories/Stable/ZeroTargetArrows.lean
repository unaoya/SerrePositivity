module
public import SerrePositivity.InfinityCategories.Stable.TerminalPrismBoundary
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.Stable.SuspensionDiagrams

/-! # 零対象へ向かう辺の族

概要：零対象を終点に持つ辺全体から始点への評価は trivial Kan fibration。
方針：正次元は終対象を持つ prism の境界延長、零次元は零対象への辺の存在を使う。
規約：零対象を一つに固定せず、全部分圏内で動かす。
使われ方：S3 の suspension の span の族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：関手区間の頂点の終点が零対象であるという条件。
方針：時刻一で評価する。
規約：辺の始点は自由に動く。
使われ方：零対象に向かう辺の全部分圏。 -/
def IsZeroTargetArrow {X : SSet.{u}} (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  IsZeroVertex ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
    (Opposite.op ⦋0⦌) v)

/-- 概要：終点が零対象である辺の全部分単体集合。
方針：終点の頂点条件で関手単体集合の全部分複体を取る。
規約：高次単体は実際の辺の族。
使われ方：suspension の span を二本の辺から構成する。 -/
def zeroTargetArrows (X : SSet.{u}) : SSet.{u} :=
  (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) IsZeroTargetArrow : SSet.{u})

/-- 概要：零対象へ向かう辺の始点を評価する。
方針：全部分圏の包含の後で時刻零を評価する。
規約：高次単体で自然。
使われ方：suspension の入力の図式の族。 -/
def zeroTargetArrowSource (X : SSet.{u}) : zeroTargetArrows X ⟶ X :=
  (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 概要：零対象へ向かう辺の始点評価は trivial Kan fibration。
方針：正次元は終点の終対象性で prism を延長し、全頂点の零終点条件を境界から移す。
規約：零対象の存在のみを要求し、安定性は不要。
使われ方：S3 の span の入力と始点の比較。 -/
instance zeroTargetArrowSource_trivialKanFibration (X : SSet.{u}) [HasZeroVertex X] :
    TrivialKanFibration (zeroTargetArrowSource X) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    let z := chosenZeroVertex X
    obtain ⟨e⟩ := z.isTerminal.nonempty_edge (SSet.yonedaEquiv b)
    let F : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm e.edge
    let w : (zeroTargetArrows X) _⦋0⦌ := ⟨functorVertex F, by
      intro α
      have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
      unfold IsZeroTargetArrow
      rw [evaluateFunctorAt_functorVertex]
      have he := congrArg SSet.yonedaEquiv (edgeSimplex_target e)
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at he
      have hδ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) :
          (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by decide
      rw [hδ] at he
      rw [he]
      exact z.isZero⟩
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm w
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
      (Opposite.op ⦋0⦌) (functorVertex F) = _
    rw [evaluateFunctorAt_functorVertex]
    have he := congrArg SSet.yonedaEquiv (edgeSimplex_source e)
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at he
    have hδ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
    simpa only [hδ] using he
  | succ n =>
    let ι := (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) IsZeroTargetArrow).ι
    let H := uncurry (a ≫ ι)
    have hC : curry H = a ≫ ι := curry_uncurry _
    have h₀ : (boundary (n + 1)).ι ≫ b =
        prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H := by
      rw [← curry_evaluateFunctorAt_interval, hC]
      exact sq.w.symm
    have ht (v : (boundary (n + 1) : SSet.{u}) _⦋0⦌) :
        IsTerminalVertex (H.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), v)) := by
      have hz := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) v)
      exact hz.2
    obtain ⟨F, hF, hF₀⟩ := stable_prism_extend_terminal_boundary n H b h₀ ht
    have hc : (boundary (n + 1)).ι ≫ curry F = a ≫ ι := by
      rw [← curry_natural_left, hF, hC]
    have hv (v : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
        IsZeroTargetArrow ((curry F).app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
        have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) w
      change (curry F).app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at he
      rw [he]
      exact fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    let g := fullSubcomplexLift IsZeroTargetArrow (curry F) hv
    have hg : g ≫ ι = curry F := fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono ι).1
      rw [Category.assoc, hg, hc]
    · change g ≫ ι ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = b
      rw [← Category.assoc, hg, curry_evaluateFunctorAt_interval, hF₀]

end SerrePositivity.InfinityCategories
