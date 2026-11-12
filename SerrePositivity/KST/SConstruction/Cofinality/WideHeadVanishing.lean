module
public import SerrePositivity.KST.SConstruction.Cofinality.WideHeadDiscretization

/-!
概要：元の全辺 wide 図式の先頭実現の高次障害を消去する。
方針：元の自然な離散化の弱同値と元の bar 同型を通じて Sp-8 (2) 入力を移す。
規約：一般群 nerve 消滅を明示入力に保持し、相対 fiber 本体を仮定で置換しない。
使われ方：同じ元の相対旗実現から元の K 射への接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の wide 図式の先頭実現の二次以上のホモトピーは一意。
方針：元の離散化の Kan 置換の全基点 π 単射性で bar の消滅を引き戻す。
規約：元の全 S 多次数を保持し、モデル構造の instance を要求しない。
使われ方：相対 fiber 列の右項の高次消滅。 -/
lemma completionWideHead_higher_of_input (h : GroupNerveHigherVanishingInput.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (completionWideHeadRealization r ι f hf)) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (completionWideHeadRealization r ι f hf)) n x) := by
  let p := completionWideHeadDiscretization r ι f hf
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence p
    (completionWideHeadDiscretization_isWeak r ι f hf)
  have hπ := Spectra.kanPiIsomorphism_of_qCatEquivalence _
    hw.isSimplicialHomotopyEquivalence.isQCatEquivalence
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      (completionCokernelHeadIndex r ι ⋙ completionWideComponentDiagram (r + 1) f hf)) n
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map p).app (Opposite.op ⦋0⦌) x)) :=
    completionWideComponentHead_higher_of_input h r ι f hf n hn _
  exact Function.Injective.subsingleton ((hπ x n).1)

end SerrePositivity.KST.SConstruction.Cofinality
