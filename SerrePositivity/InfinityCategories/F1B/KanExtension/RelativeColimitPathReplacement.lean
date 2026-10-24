module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeColimitTrivialComparison
public import SerrePositivity.InfinityCategories.F1B.KanExtension.PathReplacementLifting

/-!
概要：可逆 path 置換による標準の相対余極限の保存と反映。
方針：二つの端点評価と始域への射影の自明 Kan 性を coslice で消去する。
規約：元の関手 U に充填性を要求しない。
使われ方：相対 Kan 拡張の局所入力を右持ち上げ可能な関手へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：path 置換上の余錐が相対余極限であることは元の始域への像で検出できる。
方針：終点評価を始点評価へ取り替え、引き戻しの可換性と射影の自明 Kan 性を使う。
規約：全ての比較は指定された余錐の像についての同値であり、余錐を選び直さない。
使われ方：一般の関手の相対余極限から path 置換上の局所余極限への移送。 -/
lemma kanIsRelativeColimitCone_equivalencePathReplacement_iff
    {K D E : SSet.{u}} [Quasicategory D] [Quasicategory E] (U : D ⟶ E)
    {F : K ⟶ equivalencePathReplacement U} (c : JoinCocone F) :
    IsRelativeColimitCone (equivalencePathReplacementMap U) c ↔
      IsRelativeColimitCone U
        ((sliceUnderPostcomp F (equivalencePathReplacementProjection U)).app
          (Opposite.op ⦋0⦌) c) := by
  let a := pullback.fst (equivalencePathEndpoint E 0) U
  have he : a ≫ equivalencePathEndpoint E 0 =
      equivalencePathReplacementProjection U ≫ U := pullback.condition
  have hh := congrArg (fun V : equivalencePathReplacement U ⟶ E ↦
    IsRelativeColimitCone V c) he
  exact (kanIsRelativeColimitCone_comp_iff_of_trivialKanFibration a
    (equivalencePathEndpoint E 1) c).trans
    ((kanIsRelativeColimitCone_comp_iff_of_trivialKanFibration a
      (equivalencePathEndpoint E 0) c).symm.trans
      (Iff.of_eq hh |>.trans
        (kanIsRelativeColimitCone_precomp_iff_of_trivialKanFibration
          (equivalencePathReplacementProjection U) U c)))

end SerrePositivity.InfinityCategories.F1B
