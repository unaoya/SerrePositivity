module
public import SerrePositivity.KST.SConstruction.Pointed
public import SerrePositivity.KST.SConstruction.GappedDegenerateSquares
public import SerrePositivity.KST.SConstruction.FirstRowPositiveBoundary

/-! # 第一行制限の低次数
概要：第一行制限の一般の問題を頂点の存在に還元し、次数1の存在を証明する。
方針：正次元の境界 RLP を既存の証明から使い、零次元には零対角図式の構成を適用する。
規約：一般次数の頂点の存在は仮定として明記する。
使われ方：BGT Lemma 7.3 の S_0・S_1 の基底段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：安定な quasicategory の第一行制限は頂点で全射なら trivial Kan fibration。
方針：零次元の境界には全射性を、正次元には既存の相対補完を使う。
規約：頂点の存在を結論済みとして扱わない。
使われ方：一般の L1b の残る存在条件と低次数の完成。 -/
lemma firstRowRestriction_trivialKanFibration_of_vertexSurjective (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (hs : Function.Surjective ((firstRowRestriction n C).app (Opposite.op ⦋0⦌))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (firstRowRestriction n C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro r
  cases r with
  | zero =>
    constructor
    intro a b sq
    obtain ⟨v, hv⟩ := hs (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hv
  | succ r => exact firstRowRestriction_hasLiftingProperty_boundary n r C

/-- 概要：次数1の第一行の任意の頂点は gapped 図式に厳密に持ち上がる。
方針：零対角 Ar[1] 図式を構成し、全ての区間正方形が退化することを使う。
規約：C は安定な quasicategory。使われ方：次数1の零次元の境界 RLP。 -/
lemma firstRowRestriction_one_vertex_surjective (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    Function.Surjective ((firstRowRestriction 1 C).app (Opposite.op ⦋0⦌)) := by
  intro d
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (firstRowNerve 1) C).symm d
  obtain ⟨F, hF, hz⟩ := exists_firstRowDiagramWithZeroDiagonal 1 C p
  let v : (sConstruction 1 C) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve 1) C).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C F))
    rw [Equiv.symm_apply_apply]
    exact isGapped_one_of_zero_diagonal F hz⟩
  refine ⟨v, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (firstRowInclusion 1 ≫ F) = d
  rw [hF]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply d

/-- 概要：次数1の第一行制限は trivial Kan fibration。
方針：頂点の全射性と全ての正次元の境界 RLP を合わせる。
規約：C は安定な quasicategory。使われ方：S_1 と C の比較の基底。 -/
instance firstRowRestriction_one_trivialKanFibration (C : SSet.{u}) [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (firstRowRestriction 1 C) :=
  firstRowRestriction_trivialKanFibration_of_vertexSurjective 1 C
    (firstRowRestriction_one_vertex_surjective C)

end SerrePositivity.KST.SConstruction
