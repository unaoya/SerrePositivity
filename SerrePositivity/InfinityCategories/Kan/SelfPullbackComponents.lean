module

public import SerrePositivity.InfinityCategories.Kan.SelfPullbackConnectingSwap
public import SerrePositivity.InfinityCategories.Kan.FiberInclusionComponents

/-!
概要：連結な全空間の自己 pullback の全成分を連結写像で代表する。
方針：第二射影の fiber の全射性を元の fiber への射で戻す。
規約：収縮可能性より弱い連結性だけで全射性を示す。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6。三角形交換の逆元の式を全成分へ適用する。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 全空間を持つ fibration の自己 pullback は Kan。
方針：第二射影の fibration と全空間の終対象への fibration を合成する。
規約：底の Kan 性はこの主張には不要。
使われ方：Kerodon §3.1.1。自己 pullback の零次数の完全列。 -/
instance selfPullback_kanComplex {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [KanComplex E] : KanComplex (pullback p p) := by
  have : Fibration (pullback.snd p p) := fibration_pullback_snd p p
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
    (e : E _⦋0⦌) : Function.Surjective (mapπ₀ (selfPullbackFiberInclusion p e)) := by
  let q := pullback.snd p p
  have : Fibration q := fibration_pullback_snd p p
  let u := (selfPullbackFiberInclusion p e).app _ (fiberPoint p e)
  have hu : q.app _ u = e := by
    have h : selfPullbackFiberInclusion p e ≫ q = SSet.const e := pullback.lift_snd _ _ _
    simpa [SSet.const, u] using
      congrArg (fun k : KanFiber p (p.app _ e) ⟶ E => k.app _ (fiberPoint p e)) h
  let φ : KanFiber q e ⟶ KanFiber p (p.app _ e) :=
    fiberLift p (p.app _ e) (fiberι q e ≫ pullback.fst p p) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (fiberι q e ≫ q) ≫ p = _
      rw [fiberι_comp, SSet.const_comp])
  have hφ : φ ≫ selfPullbackFiberInclusion p e = fiberι q e := by
    apply pullback.hom_ext
    · simp only [φ, selfPullbackFiberInclusion, Category.assoc, pullback.lift_fst,
        fiberLift_ι]
    · simp only [selfPullbackFiberInclusion, Category.assoc, pullback.lift_snd,
        SSet.comp_const]
      exact (fiberι_comp q e).symm
  intro a
  obtain ⟨b, hb⟩ := fiberInclusion_piZero_surjective_at q u e hu a
  refine ⟨mapπ₀ φ b, ?_⟩
  rw [← mapπ₀_comp_apply, hφ]
  exact hb

/-- 概要：連結な全空間の自己 pullback の全成分は底の基本群の連結射で表せる。
方針：元の fiber への連結射と自己 pullback への包含の二つの全射性を合成する。
規約：全空間と底は Kan。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6。二つの三角形の交換の全成分での計算。 -/
theorem selfPullbackConnecting_surjective {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    [Subsingleton (π₀ E)] (e : E _⦋0⦌) :
    Function.Surjective (selfPullbackConnecting p e) := by
  intro a
  obtain ⟨b, rfl⟩ := selfPullbackFiberInclusion_surjective p e a
  obtain ⟨c, hc⟩ := (componentConnecting_exact p e (p.app _ e) rfl b).1
    (Subsingleton.elim _ _)
  exact ⟨c, congrArg (mapπ₀ (selfPullbackFiberInclusion p e)) hc⟩

end

end SerrePositivity.KST.Spectra
