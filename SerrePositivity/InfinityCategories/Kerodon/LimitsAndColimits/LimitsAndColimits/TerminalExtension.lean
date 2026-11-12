module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SkeletalExtension

/-!
概要：新しい単体の最後の頂点が終対象へ写る場合の写像の延長。
方針：相対骨格の各非退化単体の境界を終対象性で充填する。
規約：指定部分は全頂点を含み、その上の射を厳密に固定する。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の極限側、関手 ∞ 圏の終対象の点ごとの判定。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：単体の最後の頂点。
方針：対応する標準単体からの射を最後の標準頂点で評価する。
規約：零次元でも定義する。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の双対の終点の条件。 -/
def simplexLastVertex {B : SSet.{u}} {n : ℕ} (s : B _⦋n⦌) : B _⦋0⦌ :=
  (SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))

/-- 概要：指定部分の外の各単体の終点が終対象なら、その部分上の射は全体へ延長する。
方針：全頂点が指定部分にあるため新しい正次元のセルの終点を固定でき、境界を終対象性で充填する。
規約：周囲の単体集合や標的の quasicategory 性を仮定しない。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の空図式の場合の双対。 -/
lemma exists_extension_of_terminal_last_vertices {B X : SSet.{u}} (A : B.Subcomplex)
    (hA : ∀ v : B _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌)) (a : (A : SSet.{u}) ⟶ X)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (a.app (Opposite.op ⦋0⦌) ⟨simplexLastVertex s, hA _⟩)) :
    ∃ F : B ⟶ X, A.ι ≫ F = a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_extension_of_skeletal_extensions A.ι a
  intro d f hf
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_extension_skeletonOfMono_succ A.ι d f
  intro c
  cases d with
  | zero =>
    exact False.elim (c.notMem ⟨⟨c.simplex, hA c.simplex⟩, rfl⟩)
  | succ n =>
    let z : (A : SSet.{u}) _⦋0⦌ := ⟨simplexLastVertex c.simplex, hA _⟩
    have hc : c.simplex ∉ A.obj (Opposite.op ⦋n + 1⦌) :=
      fun h ↦ c.notMem ⟨⟨c.simplex, h⟩, rfl⟩
    have hterm := ht n c.simplex hc
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫
        (c.ιSigmaBoundary ≫ t A.ι (n + 1)) =
          SSet.yonedaEquiv.symm z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase A.ι (n + 1) := by
      apply (cancel_mono (skeletonOfMono A.ι (n + 1)).ι).1
      have hcι : c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫
          (skeletonOfMono A.ι (n + 1)).ι = (boundary (n + 1)).ι ≫ c.map := by
        simp [Cell.ιSigmaBoundary, t]
      simp only [Category.assoc]
      rw [hcι]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase, Subcomplex.lift_ι,
        SSet.yonedaEquiv_symm_comp]
      rfl
    apply hterm n (c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫ f)
    have hw := congrArg (fun g ↦ g ≫ f) hb
    simp only [Category.assoc] at hw
    rw [hf, SSet.yonedaEquiv_symm_comp] at hw
    simpa only [Category.assoc] using hw

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
