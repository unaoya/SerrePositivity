module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PrismEvaluation

/-!
概要：元の右 coherent 区間族を、同じ単体の切断による豊穣図式として表示する。
方針：既存の prism の全単体評価式を使い、零・一の対象を正規化する。
規約：元の標準 Hom 比較を変更せず、局所 Kan 性も要求しない。
使われ方：元の分類先の第一三角形の高次 Hom 作用の計算。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 同じ右 Hom の単体を、時刻ラベルの切断で制限した実際の coherent 図式。 -/
def coherentRightIntervalCutSimplex
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Y) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    (SimplicialNerve C) _⦋n⦌ :=
  (SimplicialNerve C).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)).op
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex s)

/-- 元の標準区間族の全単体での値は、同じ切断した豊穣図式そのもの。 -/
lemma coherentHomIntervalComparison_evaluate_cut
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y)).app
        (Opposite.op ⦋n⦌) (t, ULift.up s) =
      coherentRightIntervalCutSimplex s (stdSimplex.objEquiv t).toOrderHom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pinchedHomToIntervalMappingSpace_evaluate (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y) (ULift.up s) t

/-- 切断時刻零の対象は、元の始域対象。 -/
lemma coherentRightIntervalCutSimplex_obj_zero
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Y) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i = 0) :
    (coherentRightIntervalCutSimplex s t).obj ⟨ULift.up i⟩ = X := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t i) = X
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero t i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast]

/-- 切断時刻一の対象は、元の終域対象。 -/
lemma coherentRightIntervalCutSimplex_obj_one
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Y) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i = 1) :
    (coherentRightIntervalCutSimplex s t).obj ⟨ULift.up i⟩ = Y := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t i) = Y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t i (by rw [hi]; decide), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
