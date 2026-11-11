module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialHornRestrictionLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SkeletalLifting

/-!
概要：射の上で始点を固定した境界充填と相対的な延長。
方針：各セルで指定された標的の単体を固定して持ち上げる。
規約：厳密な境界持ち上げの条件を命題として定義する。
使われ方：Kerodon §7.1.5（Tag 02WE）–7.1.8（Tag 02X8） の相対極限の境界判定への準備。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BFunctorCategoriesRelativeInitialExtension

/-- 概要：始点での相対境界充填条件から、指定部分と標的を固定した延長が得られる。
方針：新しい正次元のセルの境界を標的の上で充填し、相対骨格に沿って貼る。
規約：指定部分は全ての頂点を含む。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の相対的なセル延長の核。 -/
lemma exists_lift_of_initial_first_vertices {B X Y : SSet.{u}} (A : B.Subcomplex)
    (hA : ∀ v : B _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌))
    (p : X ⟶ Y) (a : (A : SSet.{u}) ⟶ X) (b : B ⟶ Y) (hw : a ≫ p = A.ι ≫ b)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, hA _⟩)) :
    ∃ F : B ⟶ X, A.ι ≫ F = a ∧ F ≫ p = b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_of_skeletal_lifts A.ι p a b hw
  intro d f hf hfp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_skeletonOfMono_succ A.ι p b d f hfp
  intro c
  cases d with
  | zero =>
    exact False.elim (c.notMem ⟨⟨c.simplex, hA c.simplex⟩, rfl⟩)
  | succ n =>
    let z : (A : SSet.{u}) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex c.simplex, hA _⟩
    have hc : c.simplex ∉ A.obj (Opposite.op ⦋n + 1⦌) :=
      fun h ↦ c.notMem ⟨⟨c.simplex, h⟩, rfl⟩
    have hterm := ht n c.simplex hc
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n ((0 : Fin (n + 2))) ≫
        (c.ιSigmaBoundary ≫ t A.ι (n + 1)) =
          SSet.yonedaEquiv.symm z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase A.ι (n + 1) := by
      apply (cancel_mono (skeletonOfMono A.ι (n + 1)).ι).1
      have hcι : c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫
          (skeletonOfMono A.ι (n + 1)).ι = (boundary (n + 1)).ι ≫ c.map := by
        simp [Cell.ιSigmaBoundary, t]
      simp only [Category.assoc]
      rw [hcι]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase, Subcomplex.lift_ι,
        SSet.yonedaEquiv_symm_comp]
      rfl
    have hend : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n ((0 : Fin (n + 2))) ≫
        (c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫ f) =
          SSet.yonedaEquiv.symm (a.app (Opposite.op ⦋0⦌) z) := by
      have hw' := congrArg (fun g ↦ g ≫ f) hb
      simp only [Category.assoc] at hw'
      rw [hf, SSet.yonedaEquiv_symm_comp] at hw'
      exact hw'
    have hs : CommSq (c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫ f)
        (boundary (n + 1)).ι p (c.map ≫ b) := by
      constructor
      simp only [Category.assoc]
      rw [hfp, ← Category.assoc (t A.ι (n + 1))]
      have hcι : c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫
          (skeletonOfMono A.ι (n + 1)).ι = (boundary (n + 1)).ι ≫ c.map := by
        simp [Cell.ιSigmaBoundary, t]
      simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ b) hcι
    exact hterm n _ _ hend hs

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BFunctorCategoriesRelativeInitialExtension
