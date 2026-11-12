module
public import SerrePositivity.KST.SConstruction.ArTwoExtension
public import SerrePositivity.KST.SConstruction.FirstRowLowDegrees

/-! # 次数2の第一行制限
概要：一つの射の cofiber を用いて第一行から gapped Ar[2] 図式を構成する。
方針：中央正方形に cofiber を配置し、両端に零対象を補う。
規約：第一行を厳密に回収する。使われ方：BGT Lemma 7.3 の次数2の全境界持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：次数2の第一行は中央正方形の下辺。
方針：二つの標準頂点で区間を計算する。
規約：標準辺と第一行の同型を明示する。使われ方：cofiber の入力の回収。 -/
lemma firstRow_two_middle_bottom :
    (firstRowSimplexIso 1).hom ≫ firstRowInclusion.{u} 2 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ arTwoMiddleSquare := by
  apply SSet.yonedaEquiv.injective
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  fin_cases r <;> rfl

/-- 概要：安定な quasicategory の任意の次数2の第一行は gapped 図式へ厳密に延びる。
方針：与えられた射の cofiber 正方形を中央に配置する。
規約：安定性の cofiber 存在から実際の正方形を選ぶ。
使われ方：第一行制限の零次元の境界 RLP。 -/
lemma exists_gapped_arTwo_with_firstRow (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : firstRowNerve 2 ⟶ C) :
    ∃ F : arNerve 2 ⟶ C, IsGapped F ∧ firstRowInclusion 2 ≫ F = p := by
  let e := (firstRowSimplexIso 1).hom ≫ p
  let t := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e))
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = e := by
    rw [t.bottom_edge]
    exact SSet.yonedaEquiv.symm_apply_apply e
  obtain ⟨F, hF, hmid⟩ := exists_gapped_arTwo_of_cofiber t.toZeroTriangle t.isPushout
  refine ⟨F, hF, ?_⟩
  apply (cancel_epi (firstRowSimplexIso 1).hom).1
  rw [← Category.assoc, firstRow_two_middle_bottom, Category.assoc, hmid]
  exact ht

/-- 概要：次数2の第一行制限は頂点で全射。
方針：構成した実際の gapped 図式を全部分複体の頂点にする。
規約：条件を追加仮定せず構成した証明を使用する。
使われ方：次数2の trivial Kan fibration の零次元。 -/
lemma firstRowRestriction_two_vertex_surjective (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    Function.Surjective ((firstRowRestriction 2 C).app (Opposite.op ⦋0⦌)) := by
  intro d
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (firstRowNerve 2) C).symm d
  obtain ⟨F, hF, hp⟩ := exists_gapped_arTwo_with_firstRow C p
  let v : (sConstruction 2 C) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve 2) C).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C F))
    rw [Equiv.symm_apply_apply]
    exact hF⟩
  refine ⟨v, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (firstRowInclusion 2 ≫ F) = d
  rw [hp]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply d

/-- 概要：次数2の第一行制限は trivial Kan fibration。
方針：実際の頂点の構成と全正次元の相対境界持ち上げを合わせる。
規約：C は安定な quasicategory。使われ方：S_2 の完全な第一行比較。 -/
instance firstRowRestriction_two_trivialKanFibration (C : SSet.{u}) [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (firstRowRestriction 2 C) :=
  firstRowRestriction_trivialKanFibration_of_vertexSurjective 2 C
    (firstRowRestriction_two_vertex_surjective C)

end SerrePositivity.KST.SConstruction
