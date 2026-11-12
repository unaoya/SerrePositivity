module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocallySmallHomTypes
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoLifting

/-!
概要：二つの小さい対象族と標的の同型から、引き戻し内の小さい候補族を構成する。
方針：標的の同型を小さい型へ縮小し、一方の同値持ち上げで像を厳密に合わせる。
規約：候補の compact 性や生成性は別に証明し、ここでは存在を仮定しない。
使われ方：presentable 圏の引き戻しの生成模型。

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

/-- 概要：像が厳密に一致する二頂点を元の引き戻しの頂点にする。
方針：零単体を表す射を引き戻しへ持ち上げる。
規約：元の両頂点を保持する。使われ方：候補族の各対象。 -/
def pullbackVertex {E D B : SSet.{u + 1}} (p : E ⟶ B) (q : D ⟶ B)
    (x : E _⦋0⦌) (y : D _⦋0⦌)
    (h : p.app (Opposite.op ⦋0⦌) x = q.app (Opposite.op ⦋0⦌) y) :
    (pullback p q) _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)
    (by rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h]))

/-- 概要：構成した引き戻し頂点の第一成分。
方針：元の持ち上げの第一脚を計算する。
規約：厳密な頂点の等式。使われ方：候補の compact 性の成分。 -/
lemma pullbackVertex_fst {E D B : SSet.{u + 1}} (p : E ⟶ B) (q : D ⟶ B)
    (x : E _⦋0⦌) (y : D _⦋0⦌)
    (h : p.app (Opposite.op ⦋0⦌) x = q.app (Opposite.op ⦋0⦌) y) :
    (pullback.fst p q).app (Opposite.op ⦋0⦌) (pullbackVertex p q x y h) = x := by
  rw [pullbackVertex, ← SSet.yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 概要：構成した引き戻し頂点の第二成分。
方針：元の持ち上げの第二脚を計算する。
規約：厳密な頂点の等式。使われ方：候補の生成表示の成分。 -/
lemma pullbackVertex_snd {E D B : SSet.{u + 1}} (p : E ⟶ B) (q : D ⟶ B)
    (x : E _⦋0⦌) (y : D _⦋0⦌)
    (h : p.app (Opposite.op ⦋0⦌) x = q.app (Opposite.op ⦋0⦌) y) :
    (pullback.snd p q).app (Opposite.op ⦋0⦌) (pullbackVertex p q x y h) = y := by
  rw [pullbackVertex, ← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- 概要：第一成分が元の頂点と同型で、第二成分を厳密に保つ引き戻し頂点。
方針：同値持ち上げによる第一成分の取り直しを保持する。
規約：第二成分を同型への弱い一致にしない。使われ方：小さい候補族。 -/
structure PullbackVertexCandidate {E D B : SSet.{u + 1}} (p : E ⟶ B) (q : D ⟶ B)
    (x : E _⦋0⦌) (y : D _⦋0⦌) where
  vertex : (pullback p q) _⦋0⦌
  fstIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.fst p q).app (Opposite.op ⦋0⦌) vertex) x
  snd_eq : (pullback.snd p q).app (Opposite.op ⦋0⦌) vertex = y

/-- 概要：標的の同型から両成分を保つ候補を構成する。
方針：元の第一成分を終点とする同型を持ち上げ、像が厳密に一致する二頂点を合わせる。
規約：同型の存在自体は入力に明示し、全候補族の生成性は主張しない。
使われ方：小さい同型型で添字付けた候補の評価。 -/
def pullbackVertexCandidate {E D B : SSet.{u + 1}} [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (x : E _⦋0⦌) (y : D _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (q.app (Opposite.op ⦋0⦌) y) (p.app (Opposite.op ⦋0⦌) x)) :
    PullbackVertexCandidate p q x y := by
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanVertexIso_lift_target p hp x _ e
  let z := h.choose
  have hz := h.choose_spec.1
  let ez := Classical.choice h.choose_spec.2
  refine ⟨pullbackVertex p q z y hz, ?_, pullbackVertex_snd p q z y hz⟩
  simpa only [pullbackVertex_fst] using ez

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
