module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.VertexDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalExtension

/-!
概要：各頂点で相対終点境界充填を満たす持ち上げの自然な延長。
方針：離散的な頂点上の選択を相対骨格に沿って延長し、各新しいセルの最後の頂点で充填する。
規約：頂点で選んだ値は厳密に保存する。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の点ごとの極限から自然な極限錐の存在。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：各頂点で相対終点境界充填を持つ持ち上げを選べば、それらを保つ自然な持ち上げが存在する。
方針：離散的な頂点の単射を相対骨格で延長し、各正次元のセルの終点で指定した充填を使う。
規約：射のファイブレーション性や quasicategory 性は追加で仮定しない。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の極限錐の coherent な選択。 -/
lemma exists_lift_of_terminal_vertex_lifts {A E B : SSet.{u}} (p : E ⟶ B) (g : A ⟶ B)
    (x : A _⦋0⦌ → E _⦋0⦌)
    (hx : ∀ v, p.app (Opposite.op ⦋0⦌) (x v) = g.app (Opposite.op ⦋0⦌) v)
    (ht : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (x v)) :
    ∃ F : A ⟶ E, F ≫ p = g ∧ ∀ v, F.app (Opposite.op ⦋0⦌) v = x v := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap x
  have hw : a ≫ p = i ≫ g := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp p g x hx
  obtain ⟨F, hF, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_of_skeletal_lifts i p a g hw (by
    intro d f hf hfp
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_skeletonOfMono_succ i p g d f hfp
    intro c
    cases d with
    | zero =>
      exact False.elim (c.notMem ⟨c.simplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero c.simplex⟩)
    | succ n =>
      let z : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A) _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex (B := A) c.simplex
      have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫
          (c.ιSigmaBoundary ≫ t i (n + 1)) =
            SSet.yonedaEquiv.symm z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i (n + 1) := by
        apply (cancel_mono (skeletonOfMono i (n + 1)).ι).1
        have hcι : c.ιSigmaBoundary ≫ t i (n + 1) ≫
            (skeletonOfMono i (n + 1)).ι = (boundary (n + 1)).ι ≫ c.map := by
          simp [Cell.ιSigmaBoundary, t]
        simp only [Category.assoc]
        rw [hcι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
        simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase, Subcomplex.lift_ι,
          SSet.yonedaEquiv_symm_comp]
        change (SSet.yonedaEquiv.symm z : (Δ[0] : SSet.{u}) ⟶ A) =
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := A) z 0)
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      have hend : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫
          (c.ιSigmaBoundary ≫ t i (n + 1) ≫ f) = SSet.yonedaEquiv.symm (x z) := by
        have hh := congrArg (fun t ↦ t ≫ f) hb
        simp only [Category.assoc] at hh
        rw [hf, SSet.yonedaEquiv_symm_comp] at hh
        change _ = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x z) 0) at hh
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using hh
      have hs : CommSq (c.ιSigmaBoundary ≫ t i (n + 1) ≫ f)
          (boundary (n + 1)).ι p (c.map ≫ g) := by
        constructor
        simp only [Category.assoc]
        rw [hfp, ← Category.assoc (t i (n + 1))]
        have hcι : c.ιSigmaBoundary ≫ t i (n + 1) ≫
            (skeletonOfMono i (n + 1)).ι = (boundary (n + 1)).ι ≫ c.map := by
          simp [Cell.ιSigmaBoundary, t]
        simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ g) hcι
      exact ht z n _ _ hend hs)
  refine ⟨F, hFp, ?_⟩
  intro v
  have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hF (Opposite.op ⦋0⦌)) v
  change F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := A) v 0) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x v) 0 at hh
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using hh

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
