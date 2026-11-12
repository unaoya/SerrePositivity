module
public import SerrePositivity.KST.SConstruction.FundamentalLoopEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse

/-! # 既存の Kan 基本群とホモトピー圏の loop 射の同値
概要：元の基本群の商をホモトピー圏の自己射と同定し、群の積と辺の合成を照合する。
方針：境界定数一次単体と loop 辺の同値を二つのホモトピー関係の商へ降ろす。
規約：積は辺を辿る順の合成。使われ方：置換前の辺の表示から K 群の生成を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories Spectra
open scoped Simplicial

/-- 元の基本群の充填関係と、端点つき loop 辺の左ホモトピー関係は一致する。 -/
lemma fundamentalLoop_rel_iff {B : SSet.{u}} [KanComplex B] {x : B _⦋0⦌}
    (f g : B.PtSimplex 1 x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel f g ↔ SSet.Truncated.HomotopicL (fundamentalLoopEdge f) (fundamentalLoopEdge g) := by
  constructor
  · rintro ⟨h⟩
    have hc := fundamentalLoopMulToComp h
    rw [fundamentalLoopEdge_const] at hc
    exact (show SSet.Truncated.HomotopicR (fundamentalLoopEdge f)
      (fundamentalLoopEdge g) from ⟨hc⟩).homotopicL
  · intro h
    obtain ⟨hc⟩ := h.homotopicR
    have hc' : SSet.Truncated.Edge.CompStruct (fundamentalLoopEdge (.const : B.PtSimplex 1 x))
        (fundamentalLoopEdge f) (fundamentalLoopEdge g) := by
      rw [fundamentalLoopEdge_const]
      exact hc
    exact ⟨fundamentalLoopCompToMul hc'⟩

/-- 元の基本群の類を、辺のホモトピー類の圏の自己射へ写す。 -/
def fundamentalLoopToEdgeHom (B : SSet.{u}) [KanComplex B] (x : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 x →
      (SSet.Truncated.HomotopyCategory₂.mk (A := (truncation 2).obj B) x ⟶
        SSet.Truncated.HomotopyCategory₂.mk x) :=
  Quotient.lift (fun s => SSet.Truncated.HomotopyCategory₂.homMk (fundamentalLoopEdge s))
    (fun f g h => ((fundamentalLoop_rel_iff f g).mp h).congr_homotopyCategory₂HomMk)

/-- 基本群から loop 辺のホモトピー類への写像は全単射。 -/
lemma fundamentalLoopToEdgeHom_bijective (B : SSet.{u}) [KanComplex B] (x : B _⦋0⦌) :
    Function.Bijective (fundamentalLoopToEdgeHom B x) := by
  constructor
  · intro a b h
    obtain ⟨f, rfl⟩ := Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Quotient.mk_surjective b
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff f g).mpr
    exact (fundamentalLoop_rel_iff f g).mpr (Quotient.exact h)
  · intro a
    obtain ⟨e, rfl⟩ := SSet.Truncated.HomotopyCategory₂.homMk_surjective a
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (fundamentalLoopSimplex e), ?_⟩
    exact congrArg SSet.Truncated.HomotopyCategory₂.homMk
      ((fundamentalLoopEdgeEquiv B x).apply_symm_apply e)

/-- 既存の実際の基本群と、通常のホモトピー圏の基点の自己射の同値。 -/
def fundamentalLoopHomEquiv (B : SSet.{u}) [KanComplex B] (x : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 x ≃ (SSet.HomotopyCategory.mk (X := B) x ⟶
      SSet.HomotopyCategory.mk x) :=
  (Equiv.ofBijective (fundamentalLoopToEdgeHom B x) (fundamentalLoopToEdgeHom_bijective B x)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge B).fullyFaithfulFunctor.homEquiv

/-- 同値は元の境界定数単体を同じ loop 辺のホモトピー圏の類へ写す。 -/
lemma fundamentalLoopHomEquiv_mk (B : SSet.{u}) [KanComplex B] (x : B _⦋0⦌)
    (s : B.PtSimplex 1 x) :
    fundamentalLoopHomEquiv B x (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) =
      SSet.Truncated.HomotopyCategory.homMk (fundamentalLoopEdge s) := rfl

/-- 基本群の単位は基点の恒等射に対応する。 -/
lemma fundamentalLoopHomEquiv_one (B : SSet.{u}) [KanComplex B] (x : B _⦋0⦌) :
    fundamentalLoopHomEquiv B x 1 = 𝟙 _ := by
  change fundamentalLoopHomEquiv B x (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (.const : B.PtSimplex 1 x)) = _
  rw [fundamentalLoopHomEquiv_mk, fundamentalLoopEdge_const,
    SSet.Truncated.HomotopyCategory.homMk_id]
  rfl

/-- 基本群の積は、元の向きで辺を辿る順の合成に対応する。 -/
lemma fundamentalLoopHomEquiv_mul (B : SSet.{u}) [KanComplex B] (x : B _⦋0⦌)
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 x) :
    fundamentalLoopHomEquiv B x (a * b) =
      fundamentalLoopHomEquiv B x a ≫ fundamentalLoopHomEquiv B x b := by
  obtain ⟨f, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Quotient.mk_surjective b
  obtain ⟨h, ⟨hc⟩⟩ := PtSimplex.MulStruct.nonempty f g (0 : Fin 1)
  have hp := congrArg (fundamentalLoopHomEquiv B x) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hc)
  exact hp.trans (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (fundamentalLoopMulToComp hc)).symm

/-- 基本群の元で表されるホモトピー圏の自己射は可逆。 -/
instance fundamentalLoopHomEquiv_isIso (B : SSet.{u}) [KanComplex B] (x : B _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 x) : IsIso (fundamentalLoopHomEquiv B x a) :=
  IsGroupoid.all_isIso (C := hoFunctor.obj B) _

/-- 基本群の逆元は同じホモトピー圏の射の逆に対応する。 -/
lemma fundamentalLoopHomEquiv_inv (B : SSet.{u}) [KanComplex B] (x : B _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 x) :
    fundamentalLoopHomEquiv B x a⁻¹ = inv (fundamentalLoopHomEquiv B x a) := by
  apply (cancel_epi (fundamentalLoopHomEquiv B x a)).mp
  rw [← fundamentalLoopHomEquiv_mul, mul_inv_cancel, fundamentalLoopHomEquiv_one,
    IsIso.hom_inv_id]

end SerrePositivity.KST.SConstruction
