module
public import SerrePositivity.InfinityCategories.Derived.DGIdempotentCompleteGeneral
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementIdempotents
/-!
概要：実 perfect dg 加群の coherent 冪等完備性を公開する最小 dg 入口。
方針：同じ perfect dg 加群の H⁰ 分裂を一般の nerve 判定へ渡す。
規約：安定性・導来圏比較を仮定せず、全 coherent 冪等図式を分裂する。
使われ方：K-S• の実 Perf 頂点における冪等完備性の供給。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R]

/-- 概要：任意の dg 圏の coherent 完備性。方針：H⁰ の分裂を転送。
規約：Small 不要。使われ方：perfect 模型への一般判定。 -/
lemma dgNerve_coherentIdempotentComplete_of_h0 (C : Type v) [DGCategory R C]
    [CategoryTheory.IsIdempotentComplete (DifferentialGraded.HomotopyCategory R C)] :
    F2.Idempotent.IsIdempotentComplete (dgNerve R C) :=
  dgNerve_isIdempotentComplete_of_h0 R C

/-- 概要：実 perfect 加群の coherent 完備性。方針：同じ H⁰ の分裂を使用。
規約：元の dg nerve 全体を保つ。使われ方：K-S• の Perf 頂点。 -/
lemma dgPerfectModuleNerve_isIdempotentComplete
    (D : Type v) [DGCategory R D] [Small.{u} D] :
    F2.Idempotent.IsIdempotentComplete (dgNerve R (PerfectDGModule R D)) :=
  dgNerve_isIdempotentComplete_of_h0 R (PerfectDGModule R D)

/-- 概要：指定生成集合上の実 Perf の完備性。方針：同じ H⁰ 分裂を転送。
規約：生成集合を変更しない。使われ方：相対 perfect 模型。 -/
lemma dgPerfectModuleOverNerve_isIdempotentComplete
    (D : Type v) [DGCategory R D] [Small.{u} D] (S : Set D) :
    F2.Idempotent.IsIdempotentComplete (dgNerve R (PerfectDGModuleOver R D S)) :=
  dgNerve_isIdempotentComplete_of_h0 R (PerfectDGModuleOver R D S)

/-- 概要：小さい実 Perf 模型の完備性。方針：小模型自身の H⁰ 分裂を転送。
規約：元の小模型を保つ。使われ方：宇宙を固定した Perf 頂点。 -/
lemma dgSmallPerfectModuleOverNerve_isIdempotentComplete
    (D : Type v) [DGCategory R D] [Small.{u} D] (S : Set D) :
    F2.Idempotent.IsIdempotentComplete (dgNerve R (SmallPerfectDGModuleOver R D S)) :=
  dgNerve_isIdempotentComplete_of_h0 R (SmallPerfectDGModuleOver R D S)
end SerrePositivity.InfinityCategories
