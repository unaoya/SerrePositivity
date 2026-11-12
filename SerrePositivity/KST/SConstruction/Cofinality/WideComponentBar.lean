module
public import SerrePositivity.KST.SConstruction.Cofinality.MultiCokernelRow

/-!
概要：元の全 S 多次数の wide 成分図式の一方向を bar と同定する。
方針：構成済みの全多次数の障害群同型と元の余核の bar 同型を合成する。
規約：元の全辺 wide 模型の成分を使う。
使われ方：相対旗の離散化後の障害図式の高次消滅。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の全多次数の wide 成分図式の先頭方向は同じ元の余核群の bar。
方針：全多次数の自然な障害同型を先頭方向へ制限し、元の bar 同型を合成する。
規約：完備化射も残りの多次数も元の指定を保つ。
使われ方：相対実現の離散成分障害を具体的な群 nerve へ移す。 -/
def completionWideComponentHeadBarIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionCokernelHeadIndex r ι ⋙ completionWideComponentDiagram (r + 1) f hf ≅
      nerve (AsSmall.{u} (SingleObj (Multiplicative
        (cutKZeroCokernel 1 (((multiSEndofunctor r).obj ι).map f))))) :=
  Functor.isoWhiskerLeft (completionCokernelHeadIndex r ι)
      (completionWideComponentCokernelNatIso (r + 1) f hf) ≪≫
    completionCokernelHeadBarIso r ι f

/-- 概要：元の wide 成分障害図式の先頭方向の二次以上のホモトピー消滅。
方針：厳密な bar 同型で採用済み Sp-8 (2) の明示入力を移す。
規約：元の相対 fiber 本体の比較は別工程として保持する。
使われ方：同じ全 S 多次数の障害の消滅。 -/
lemma completionWideComponentHead_higher_of_input (h : GroupNerveHigherVanishingInput.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      (completionCokernelHeadIndex r ι ⋙ completionWideComponentDiagram (r + 1) f hf)) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
      (completionCokernelHeadIndex r ι ⋙ completionWideComponentDiagram (r + 1) f hf)) n x) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.mapIso (completionWideComponentHeadBarIso r ι f hf)
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (nerve (AsSmall.{u} (SingleObj (Multiplicative
        (cutKZeroCokernel 1 (((multiSEndofunctor r).obj ι).map f))))))) n
          (e.hom.app (Opposite.op ⦋0⦌) x)) :=
    cutCokernelBar_higher_of_input h 1 (((multiSEndofunctor r).obj ι).map f) n hn _
  exact Function.Injective.subsingleton ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e x n).1)

end SerrePositivity.KST.SConstruction.Cofinality
