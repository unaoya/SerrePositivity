module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedRelativeRealizationIso

/-!
概要：供給側の本質像相対実現の高次ホモトピーは追加の一般供給仮定なしで一意。
方針：元の三方向の実現同型で相対先頭実現の実証明を移す。
規約：元の本質像・元の実現・任意の基点を保持する。
使われ方：K-B2-S1 の fiber 列へ渡す右項の高次消滅。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：供給側の元の本質像相対実現の二次以上のホモトピーは一意。
方針：同じ元の相対実現同型の Kan 置換の単射で高次消滅を引き戻す。
規約：相対 fiber 本体や Sp-8 の結論を追加仮定に残さない。
使われ方：元の K 射の正次数全単射・零次単射を導く右項。 -/
theorem completionClosedRelative_higher_subsingleton (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (Fibration.Relative.closedRelativeRealization
      (completionImageClosedPredicate r ι f hf))) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (Fibration.Relative.closedRelativeRealization
        (completionImageClosedPredicate r ι f hf))) n x) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.mapIso
    (completionClosedRelativeRealizationIso r ι f hf)
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (completionRelativeHeadRealization r ι f hf)) n
        (e.hom.app (Opposite.op ⦋0⦌) x)) :=
    completionRelativeHead_higher_subsingleton r ι f hf n hn _
  exact Function.Injective.subsingleton ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e x n).1)

end SerrePositivity.KST.SConstruction.Cofinality
