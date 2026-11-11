module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationIntervalLifting
public import SerrePositivity.KST.Comparison.FibrantTargetLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveStandard

/-! # 連結な Kan 基底の非空な fibration の全単体全射性
概要：連結な Kan 基底の上の非空な Kan fibration は全単体で全射となる。
方針：零次数の fiber 輸送で頂点を持ち上げ、単体の頂点包含の局所化同型で全単体を持ち上げる。
規約：全空間の一頂点を明示する。使われ方：連結な基底での基底変換の検出性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomotopicalAlgebra SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 連結な Kan 基底の上の非空な Kan fibration は頂点で全射。 -/
lemma fibration_vertex_surjective_of_connected {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] [SSet.IsPreconnected B]
    (p : E ⟶ B) [Fibration p] (e : E _⦋0⦌) :
    Function.Surjective (p.app (Opposite.op ⦋0⦌)) := by
  let eB := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := B) (x := p.app _ e)
  have hB : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy B 0 (p.app _ e)) :=
    ⟨fun a b => eB.injective (Subsingleton.elim _ _)⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_surjective_vertices_of_zero p e
  intro b
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0, hB.elim _ _⟩

/-- Kan 基底上の Kan fibration の頂点全射性は全単体全射性を導く。 -/
lemma fibration_simplex_surjective_of_vertex_surjective {E B : SSet.{u}} [KanComplex B]
    (p : E ⟶ B) [Fibration p]
    (hs : Function.Surjective (p.app (Opposite.op ⦋0⦌))) (n : ℕ) :
    Function.Surjective (p.app (Opposite.op ⦋n⦌)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let i : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)
  let r : (Δ[n] : SSet.{u}) ⟶ Δ[0] := stdSimplex.isTerminalObj₀.from _
  have hr : IsIso (Q.map r) :=
    SimplexNerve.standardTerminal_isIso Q (Localization.inverts Q anodyneExtensions) n
  have hir : i ≫ r = 𝟙 _ := stdSimplex.isTerminalObj₀.hom_ext _ _
  have hi : IsIso (Q.map i) := by
    have hic : IsIso (Q.map i ≫ Q.map r) := by
      rw [← Q.map_comp, hir, Q.map_id]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hic
  let : Mono i := stdSimplex.isTerminalObj₀.mono_from i
  let : HasLiftingProperty i p := localizedMono_lifting_fibrantTarget i hi p
    ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)
  intro b
  let b' : (Δ[n] : SSet.{u}) ⟶ B := SSet.yonedaEquiv.symm b
  obtain ⟨e, he⟩ := hs (SSet.yonedaEquiv (i ≫ b'))
  have sq : CommSq (SSet.yonedaEquiv.symm e) i p b' := by
    constructor
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact he
  refine ⟨SSet.yonedaEquiv sq.lift, ?_⟩
  rw [← SSet.yonedaEquiv_comp, sq.fac_right]
  exact SSet.yonedaEquiv.apply_symm_apply b

/-- 連結な Kan 基底の上の非空な Kan fibration は全単体で全射。 -/
lemma fibration_simplex_surjective_of_connected {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] [SSet.IsPreconnected B]
    (p : E ⟶ B) [Fibration p] (e : E _⦋0⦌) (n : ℕ) :
    Function.Surjective (p.app (Opposite.op ⦋n⦌)) :=
  fibration_simplex_surjective_of_vertex_surjective p
    (fibration_vertex_surjective_of_connected p e) n

end SerrePositivity.KST.SConstruction
