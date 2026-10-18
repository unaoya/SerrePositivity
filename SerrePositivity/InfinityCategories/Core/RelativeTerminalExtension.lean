module

public import SerrePositivity.InfinityCategories.Core.TerminalExtension
public import SerrePositivity.InfinityCategories.Core.SkeletalLifting

/-!
概要：射の上で終点を固定した境界充填と相対的な延長。
方針：各セルで指定された標的の単体を固定して持ち上げる。
規約：厳密な境界持ち上げの条件を命題として定義する。
使われ方：Kerodon §7.1.5–7.1.8 の相対極限の境界判定への準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：終点 x を持つ正次元境界が、指定された標的の単体の上で充填できる条件。
方針：各境界の可換正方形に対する持ち上げの存在を要求する。
規約：射の inner fibration 性や quasicategory 性は定義に含めない。
使われ方：Kerodon §7.1.5–7.1.8 の相対終対象の厳密な境界テスト。 -/
def TerminalBoundaryLifting {X Y : SSet.{u}} (p : X ⟶ Y) (x : X _⦋0⦌) : Prop :=
  ∀ (n : ℕ) (a : (boundary (n + 1) : SSet.{u}) ⟶ X) (b : (Δ[n + 1] : SSet.{u}) ⟶ Y),
    boundaryVertex n (Fin.last (n + 1)) ≫ a = SSet.yonedaEquiv.symm x →
      CommSq a (boundary (n + 1)).ι p b →
        ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ F = a ∧ F ≫ p = b

/-- 概要：終点での相対境界充填条件から、指定部分と標的を固定した延長が得られる。
方針：新しい正次元のセルの境界を標的の上で充填し、相対骨格に沿って貼る。
規約：指定部分は全ての頂点を含む。
使われ方：Kerodon Proposition 7.1.8.7 の相対的なセル延長の核。 -/
lemma exists_lift_of_terminal_last_vertices {B X Y : SSet.{u}} (A : B.Subcomplex)
    (hA : ∀ v : B _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌))
    (p : X ⟶ Y) (a : (A : SSet.{u}) ⟶ X) (b : B ⟶ Y) (hw : a ≫ p = A.ι ≫ b)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      TerminalBoundaryLifting p (a.app (Opposite.op ⦋0⦌) ⟨simplexLastVertex s, hA _⟩)) :
    ∃ F : B ⟶ X, A.ι ≫ F = a ∧ F ≫ p = b := by
  apply exists_lift_of_skeletal_lifts A.ι p a b hw
  intro d f hf hfp
  apply exists_lift_skeletonOfMono_succ A.ι p b d f hfp
  intro c
  cases d with
  | zero =>
    exact False.elim (c.notMem ⟨⟨c.simplex, hA c.simplex⟩, rfl⟩)
  | succ n =>
    let z : (A : SSet.{u}) _⦋0⦌ := ⟨simplexLastVertex c.simplex, hA _⟩
    have hc : c.simplex ∉ A.obj (Opposite.op ⦋n + 1⦌) :=
      fun h ↦ c.notMem ⟨⟨c.simplex, h⟩, rfl⟩
    have hterm := ht n c.simplex hc
    have hb : boundaryVertex n (Fin.last (n + 1)) ≫
        (c.ιSigmaBoundary ≫ t A.ι (n + 1)) =
          SSet.yonedaEquiv.symm z ≫ skeletonBase A.ι (n + 1) := by
      apply (cancel_mono (skeletonOfMono A.ι (n + 1)).ι).1
      have hcι : c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫
          (skeletonOfMono A.ι (n + 1)).ι = (boundary (n + 1)).ι ≫ c.map := by
        simp [Cell.ιSigmaBoundary, t]
      simp only [Category.assoc]
      rw [hcι]
      rw [← Category.assoc, boundaryVertex_ι]
      simp only [Category.assoc, skeletonBase, Subcomplex.lift_ι,
        SSet.yonedaEquiv_symm_comp]
      rfl
    have hend : boundaryVertex n (Fin.last (n + 1)) ≫
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

end SerrePositivity.InfinityCategories
