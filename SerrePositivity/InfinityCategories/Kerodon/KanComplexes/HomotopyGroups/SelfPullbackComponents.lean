module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SelfPullbackConnectingSwap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberInclusionComponents

/-!
概要：連結な全空間の自己 pullback の全成分を連結写像で代表する。
方針：第二射影の fiber の全射性を元の fiber への射で戻す。
規約：収縮可能性より弱い連結性だけで全射性を示す。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6（Tag 00WL）。三角形交換の逆元の式を全成分へ適用する。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 全空間を持つ fibration の自己 pullback は Kan。
方針：第二射影の fibration と全空間の終対象への fibration を合成する。
規約：底の Kan 性はこの主張には不要。
使われ方：Kerodon §3.1.1（Tag 00T0）。自己 pullback の零次数の完全列。 -/
instance selfPullback_kanComplex {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [KanComplex E] : KanComplex (pullback p p) := by
  have : Fibration (pullback.snd p p) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_pullback_snd p p
  change Fibration (terminal.from (pullback p p))
  rw [show terminal.from (pullback p p) = pullback.snd p p ≫ terminal.from E from
    terminal.hom_ext _ _]
  infer_instance

/-- 概要：全空間の成分が一つなら元の fiber は自己 pullback の全成分を代表する。
方針：第二射影の fiber から第一射影を通じて元の fiber へ戻す。
規約：第二因子を指定基点に固定した包含を使う。
使われ方：Goerss–Jardine I §7。二因子の交換の式を全成分へ拡張する。 -/
theorem selfPullbackFiberInclusion_surjective {E B : SSet.{u}}
    [KanComplex E] (p : E ⟶ B) [Fibration p] [Subsingleton (π₀ E)]
    (e : E _⦋0⦌) : Function.Surjective (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e)) := by
  let q := pullback.snd p p
  have : Fibration q := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_pullback_snd p p
  let u := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)
  have hu : q.app _ u = e := by
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e ≫ q = SSet.const e := pullback.lift_snd _ _ _
    simpa [SSet.const, u] using
      congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e) ⟶ E => k.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)) h
  let φ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber q e ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p (p.app _ e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q e ≫ pullback.fst p p) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q e ≫ q) ≫ p = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, SSet.const_comp])
  have hφ : φ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q e := by
    apply pullback.hom_ext
    · simp only [φ, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion, Category.assoc, pullback.lift_fst,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
    · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion, Category.assoc, pullback.lift_snd,
        SSet.comp_const]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp q e).symm
  intro a
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberInclusion_piZero_surjective_at q u e hu a
  refine ⟨mapπ₀ φ b, ?_⟩
  rw [← mapπ₀_comp_apply, hφ]
  exact hb

/-- 概要：連結な全空間の自己 pullback の全成分は底の基本群の連結射で表せる。
方針：元の fiber への連結射と自己 pullback への包含の二つの全射性を合成する。
規約：全空間と底は Kan。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6（Tag 00WL）。二つの三角形の交換の全成分での計算。 -/
theorem selfPullbackConnecting_surjective {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    [Subsingleton (π₀ E)] (e : E _⦋0⦌) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p e) := by
  intro a
  obtain ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion_surjective p e a
  obtain ⟨c, hc⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_exact p e (p.app _ e) rfl b).1
    (Subsingleton.elim _ _)
  exact ⟨c, congrArg (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e)) hc⟩

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackConnecting_surjective := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_surjective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackFiberInclusion_surjective := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion_surjective

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullback_kanComplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullback_kanComplex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullback_kanComplex
