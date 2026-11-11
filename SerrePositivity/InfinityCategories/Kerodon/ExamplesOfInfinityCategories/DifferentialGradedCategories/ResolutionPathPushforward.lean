module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ResolutionHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionPushforward

/-!
# 解像の旗の押し出しと native Path の像

概要：旗の値域を移す操作は最終頂点を固定する native Path の像と一致する。
方針：追加した最終点と元の有限集合の像を所属で比較する。
規約：値域の単調写像は単射でなくてもよい。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の pinched 次数についての自然性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：旗から作った Path の添字変換は押し出した旗の Path に等しい。
方針：最終点固定延長の像の元を二種類に分ける。
規約：全ての単調写像と全段で成り立つ。
使われ方：Kerodon 2.5.9（Tag 00SC） の評価の pinched 次数の変更。 -/
lemma resolutionFlagPath_pushforward {m n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag m d)
    (β : ⦋m⦌ ⟶ ⦋n⦌) (t : Fin (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindex β (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath.{u} F t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath (F.pushforward β.toOrderHom) t := by
  apply SimplicialThickening.Path.ext
  apply Set.ext
  intro z
  change z ∈ (fun k : ULift.{u} (Fin (m + 2)) ↦
    ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom β.toOrderHom k.down)) ''
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath F t).I ↔ _
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases hk with hk | ⟨j, hj, rfl⟩
    · rw [Set.mem_singleton_iff.mp hk]
      exact Or.inl (ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last _))
    · apply Or.inr
      refine ⟨β.toOrderHom j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
      exact ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc _ _).symm
  · rintro (hz | ⟨j, hj, rfl⟩)
    · refine ⟨ULift.up (Fin.last (m + 1)), Or.inl rfl, ?_⟩
      exact (ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last _)).trans hz.symm
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      refine ⟨ULift.up k.castSucc, Or.inr ⟨k, hk, rfl⟩, ?_⟩
      exact ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc _ _)

/-- 概要：Path の単体の添字変換は押し出した旗の Path の単体になる。
方針：各頂点の Path の一致と包含の圏の射の一意性を使う。
規約：旗の単体次数 d は変えず、値域 m を n に変える。
使われ方：HA 1.3.1.17 の解像の余単体的構造と評価の整合。 -/
lemma resolutionFlagPathFunctor_pushforward {m n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag m d)
    (β : ⦋m⦌ ⟶ ⦋n⦌) :
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor.{u} β F.start)).app (Opposite.op ⦋d⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPathFunctor F) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPathFunctor (F.pushforward β.toOrderHom) := by
  refine CategoryTheory.Functor.ext (fun t ↦ resolutionFlagPath_pushforward F β t)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
