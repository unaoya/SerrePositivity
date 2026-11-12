module

public import SerrePositivity.KST.Spectra.FundamentalLoopHomotopyCategory
public import SerrePositivity.KST.Spectra.RelStructHomotopy

/-!
概要：元の loop 辺のホモトピー圏の類が恒等射なら、同じ区間を両端点固定で収縮する。
方針：基本群と同じ基点の自己射の単射比較で類を戻し、相対 prism ホモトピーを使う。
規約：標的は Kan。使われ方：構造比較の境界トレースから実際の二次元収縮への回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 恒等射を表す元の loop の同じ単体を、境界全体を固定して収縮する。 -/
lemma exists_loop_contraction_of_homMk_eq_id {Z : SSet.{u}} [KanComplex Z]
    {x : Z _⦋0⦌} (s : Z.PtSimplex 1 x)
    (h : SSet.HomotopyCategory.homMk (FundamentalLoop.edge s) =
      𝟙 (SSet.HomotopyCategory.mk x)) :
    ∃ K : SSet.Homotopy s.map (SSet.const x),
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ K.h =
        fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ s.map := by
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (.const : Z.PtSimplex 1 x) := by
    apply FundamentalLoop.toHom_injective
    rw [FundamentalLoop.toHom_mk, FundamentalLoop.toHom_mk,
      FundamentalLoop.edge_const, SSet.HomotopyCategory.homMk_id]
    exact h
  obtain ⟨H⟩ := (KanHomotopyGroup.mk_eq_iff_relativeHomotopy s .const).1 hc
  let K : SSet.Homotopy s.map (SSet.const x) := {
    h := H.h
    h₀ := H.h₀
    h₁ := H.h₁
    rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim }
  refine ⟨K, ?_⟩
  have hs : (boundary 1).ι ≫ s.map = SSet.const x := by
    simpa only [Subcomplex.ofSimplex_ι, SSet.comp_const] using s.comm
  change (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h = _
  rw [hs]
  simpa only [Subcomplex.ofSimplex_ι, SSet.comp_const] using H.rel

/-- 元の区間を境界固定で収縮できれば、元の loop 辺の類は恒等射。 -/
lemma homMk_eq_id_of_loop_contraction {Z : SSet.{u}} [KanComplex Z]
    {x : Z _⦋0⦌} (s : Z.PtSimplex 1 x) (K : SSet.Homotopy s.map (SSet.const x))
    (hb : (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ K.h =
      fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ s.map) :
    SSet.HomotopyCategory.homMk (FundamentalLoop.edge s) =
      𝟙 (SSet.HomotopyCategory.mk x) := by
  let H : s.Homotopy (.const : Z.PtSimplex 1 x) := {
    h := K.h
    h₀ := K.h₀
    h₁ := K.h₁
    rel := by
      rw [hb, s.comm] }
  have h := congrArg FundamentalLoop.toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.eq_of_relativeHomotopy H)
  rw [FundamentalLoop.toHom_mk, FundamentalLoop.toHom_mk,
    FundamentalLoop.edge_const, SSet.HomotopyCategory.homMk_id] at h
  exact h

end SerrePositivity.KST.Spectra
