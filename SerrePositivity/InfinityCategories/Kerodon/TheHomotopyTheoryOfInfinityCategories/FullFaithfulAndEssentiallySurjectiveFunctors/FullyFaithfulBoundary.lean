module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.StdSimplexTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection

/-!
概要：充満忠実な inner fibration の正次元境界の持ち上げ。
方針：標準単体へ引き戻し、最後の頂点の終対象性を反映して境界を充填する。
規約：零次元の境界には別に頂点上の全射性を課す。
使われ方：Kerodon Proposition 4.8.4.5（Tag 05AR） の全次元の境界判定。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：充満忠実な inner fibration は正次元の全境界を持ち上げる。
方針：標準単体上の基底変換で最後の頂点の終対象性を反映し、標準単体への射を頂点で比較する。
規約：頂点上の全射性は不要。
使われ方：Kerodon Proposition 4.8.4.5（Tag 05AR） の n≥1 の場合。 -/
lemma IsFullyFaithful.hasLiftingProperty_boundary_succ {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (n : ℕ) : HasLiftingProperty (boundary (n + 1)).ι p := by
  constructor
  intro a b sq
  let q := pullback.snd p b
  have : InnerFibration q := ⟨innerFibrations.pullback_snd p b (InnerFibration.mem (q := p))⟩
  have : Quasicategory (pullback p b) := quasicategory_of_innerFibration q
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q := hp.pullback_snd b
  let a' := pullback.lift a (boundary (n + 1)).ι sq.w
  have ha' : a' ≫ q = (boundary (n + 1)).ι := pullback.lift_snd _ _ _
  let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ a')
  have htq : q.app (Opposite.op ⦋0⦌) t = stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)) := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, ha', _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι, Equiv.apply_symm_apply]
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex t := hq.reflects_isTerminalVertex (by
    rw [htq]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.stdSimplex_last_isTerminalVertex (n + 1))
  obtain ⟨F, hF⟩ := ht n a' (SSet.yonedaEquiv.symm_apply_apply _).symm
  have hFq : F ≫ q = 𝟙 Δ[n + 1] := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_of_subcomplex_vertices (boundary (n + 1))
      (fun v ↦ by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h)
    rw [← Category.assoc, hF, ha', Category.comp_id]
  refine CommSq.HasLift.mk' { l := F ≫ pullback.fst p b, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, hF]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (F ≫ q) ≫ b = b
    rw [hFq, Category.id_comp]

/-- 概要：頂点上で全射な充満忠実 inner fibration は trivial Kan fibration。
方針：正次元の境界を前の補題で持ち上げ、零次元では頂点を選ぶ。
規約：本質的全射性だけではなく零単体上の全射性をこの補題に仮定する。
使われ方：Kerodon Proposition 4.8.4.5（Tag 05AR） の同値判定への還元。 -/
lemma IsFullyFaithful.trivialKanFibration_of_surjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (hs : Function.Surjective (p.app (Opposite.op ⦋0⦌))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  cases n with
  | zero =>
    constructor
    intro a b sq
    obtain ⟨x, hx⟩ := hs (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm x
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    rw [SSet.yonedaEquiv_symm_comp, hx, Equiv.symm_apply_apply]
  | succ n => exact hp.hasLiftingProperty_boundary_succ n

/-- 概要：頂点上で全射な充満忠実 inner fibration は A3a の同値。
方針：全境界の持ち上げから明示的な逆射と可逆二胞体を選ぶ。
規約：一般の本質的全射な関手の判定への還元に用いる。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX）、Proposition 4.8.4.5（Tag 05AR）。 -/
lemma IsFullyFaithful.isQCatEquivalence_of_surjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (hs : Function.Surjective (p.app (Opposite.op ⦋0⦌))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p := by
  have := hp.trivialKanFibration_of_surjective hs
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration p

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
