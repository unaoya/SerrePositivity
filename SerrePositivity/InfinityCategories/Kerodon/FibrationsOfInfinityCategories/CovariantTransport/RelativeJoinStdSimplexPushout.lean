module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinLastCellLift
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：最後の頂点を保つ標準単体間の射の relative join の境界と prism による pushout。
方針：最後のセルへの持ち上げで被覆を示し、逆像の pullback と境界外の単射性を使う。
規約：通常の単体集合の pushout を構成する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、f(m)=n の場合の比較の立方体の後面。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：最後の頂点を保つ場合、relative join は境界 relative join と prism で覆われる。
方針：境界に入らない単体の右成分を終端に固定し、最後の prism セルへ持ち上げる。
規約：各次数 d の全ての単体について二つの射の像による被覆を結論する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、後面の pushout の全射性の検査。 -/
lemma relativeJoin_stdSimplex_boundary_or_prism {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Δ[n])) _⦋d⦌) :
    z ∈ Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Δ[n]) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app (Opposite.op ⦋d⦌)) ∨
      z ∈ Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f).app (Opposite.op ⦋d⦌)) := by
  let p := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n])
  let s := p.app (Opposite.op ⦋d⦌) z
  by_cases hs : s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary m) Δ[n]).obj (Opposite.op ⦋d⦌)
  · obtain ⟨b, hb⟩ := hs
    have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_isPullback (𝟙 Δ[n])
      (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl).app (Opposite.op ⦋d⦌)
    obtain ⟨a, ha, _⟩ := Types.exists_of_isPullback hp z b hb.symm
    exact Or.inl ⟨a, ha⟩
  · let tc := (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n])).app (Opposite.op ⦋d⦌) z
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])).app (Opposite.op ⦋d⦌) s =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n]).app (Opposite.op ⦋d⦌) (tc.1, tc.2) :=
      congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Δ[n]) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[n] ↦
        k.app (Opposite.op ⦋d⦌) z)
          (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n]))
    have htail := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_stdSimplex_right_tail_last f hf s tc.1 tc.2 he hs
    apply Or.inr
    refine ⟨(SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m (Fin.last m))).app
      (Opposite.op ⦋d⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLastCellLiftSimplex s), ?_⟩
    apply (mono_iff_injective (p.app (Opposite.op ⦋d⦌))).mp inferInstance
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLastCellLiftSimplex_fst f hf s htail

/-- 概要：最後の頂点を保つ標準単体間の射の境界 relative join と prism の正方形は pushout。
方針：既知の pullback に、二つの射の像の被覆と境界の外での単射性を適用する。
規約：m=0 と n=0 も含む全ての標準単体の次元で成立する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、標準単体の最後の頂点を保つ場合の比較の後面。 -/
lemma relativeJoin_stdSimplex_prism_isPushout {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismPenultimateBoundaryLift f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismPenultimate m).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Δ[n]) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f) := by
  apply IsPushout.of_forall_isPushout_app
  rintro ⟨⟨d⟩⟩
  apply Types.isPushout_of_isPullback_of_mono'
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismPenultimateBoundaryLift_isPullback f).app (Opposite.op ⦋d⦌))
  · apply Set.eq_univ_of_forall
    intro z
    exact relativeJoin_stdSimplex_boundary_or_prism f hf z
  · intro x y hx hy h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_injective_outside_penultimate f x y _ _ h
    · intro hx'
      exact hx ⟨⟨x, hx'⟩, rfl⟩
    · intro hy'
      exact hy ⟨⟨y, hy'⟩, rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
