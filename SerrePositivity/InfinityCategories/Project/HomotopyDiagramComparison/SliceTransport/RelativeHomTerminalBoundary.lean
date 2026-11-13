module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorRestrictionLifting

/-!
概要：相対内部 Hom の終点境界充填と、底での終点境界充填を合成する。
方針：底の関手族を先に充填し、同じ全境界データを引き戻しへ組み合わせて持ち上げる。
規約：単射性や fibration 性を仮定せず、元の相対境界充填の証拠だけを使う。
使われ方：小さい全空間に持ち上げた元の錐の極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 底と相対内部 Hom で同じ終点境界を充填できれば、元の関手制限でも充填できる。 -/
lemma terminalBoundaryLifting_pre_of_relativeHom
    {A K E B : SSet.{u}} (i : K ⟶ A) (p : E ⟶ B)
    (r : internalHom.PullbackObjObj i p) (x : ((ihom A).obj E) _⦋0⦌)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting r.π x)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting ((pre i).app B)
      (((ihom A).map p).app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting ((pre i).app E) x := by
  intro n a β ha sq
  have hend : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (a ≫ (ihom A).map p) =
      SSet.yonedaEquiv.symm (((ihom A).map p).app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
  have hbase : CommSq (a ≫ (ihom A).map p) (boundary (n + 1)).ι
      ((pre i).app B) (β ≫ (ihom K).map p) := by
    constructor
    rw [Category.assoc, (pre i).naturality p, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨γ, hγ, hγp⟩ := hb n _ _ hend hbase
  let v := r.isPullback.lift β γ hγp.symm
  have hsq : CommSq a (boundary (n + 1)).ι r.π v := by
    constructor
    apply r.hom_ext
    · rw [Category.assoc, r.π_fst, Category.assoc, r.isPullback.lift_fst]
      exact sq.w
    · rw [Category.assoc, r.π_snd, Category.assoc, r.isPullback.lift_snd]
      exact hγ.symm
  obtain ⟨F, hF, hFr⟩ := hr n a v ha hsq
  refine ⟨F, hF, ?_⟩
  have hfst : r.π ≫ r.fst = (pre i).app E := r.π_fst
  rw [← hfst, ← Category.assoc, hFr]
  exact r.isPullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
