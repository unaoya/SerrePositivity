module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UnderWeightedColimitComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitDegreeExt

/-!
概要：既存の Under の評価から作った同じ coend 比較射が同型であることを正規化で示す。
方針：各生成元を最初の構造射に沿う coend の法則で戻し、既存の標準射列の復元則を使う。
規約：Kerodon Construction 5.3.2.1（Tag 035V）の既存の replacement 模型の係数移送。
使われ方：集合値の元の圏と native BK 余極限の比較。大域の自然写像は先に構成したものを保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I]

/-- 任意の Under の生成元は、最初の構造射を係数に吸収した同じ標準生成元に等しい。 -/
lemma underWeightedColimit_normalize (F : I ⥤ SSet.{u}) {i : I} {n : ℕ}
    (τ : ComposableArrows (Under i) n) (x : (F.obj i) _⦋n⦌) :
    (weightedColimitι (underNerveWeight I) F (τ.obj 0).right).app (Opposite.op ⦋n⦌)
      ((F.map (τ.obj 0).hom).app (Opposite.op ⦋n⦌) x,
        scaffoldUnderChain (τ ⋙ Under.forget i)) =
      (weightedColimitι (underNerveWeight I) F i).app (Opposite.op ⦋n⦌) (x, τ) := by
  have h := congrArg (fun g => g.app (Opposite.op ⦋n⦌)
    (x, scaffoldUnderChain (τ ⋙ Under.forget i)))
    (weightedColimit_condition (underNerveWeight I) F (τ.obj 0).hom)
  change (weightedColimitι (underNerveWeight I) F i).app (Opposite.op ⦋n⦌)
    (x, scaffoldUnderChain (τ ⋙ Under.forget i) ⋙ Under.map (τ.obj 0).hom) = _ at h
  rw [scaffoldUnderChain_forget_factorization] at h
  exact h.symm

/-- replacement の同じ単体を、最初の頂点の指定普遍脚へ戻す点の公式。 -/
def replacementUnderWeightedPoint (F : I ⥤ SSet.{u}) (n : ℕ)
    (s : simplicialReplacementSimplex F n) : (weightedColimit (underNerveWeight I) F) _⦋n⦌ :=
  (weightedColimitι (underNerveWeight I) F (s.1.obj 0)).app (Opposite.op ⦋n⦌)
    (SSet.yonedaEquiv s.2, scaffoldUnderChain s.1)

/-- 同じ大域比較の後で点を評価すると、元の replacement の単体に戻る。 -/
lemma replacementUnderWeightedPoint_rightInverse (F : I ⥤ SSet.{u}) (n : ℕ) :
    Function.RightInverse (replacementUnderWeightedPoint F n)
      ((underWeightedColimitToReplacement F).app (Opposite.op ⦋n⦌)) := by
  intro s
  have h := congrArg (fun g => g.app (Opposite.op ⦋n⦌)
    (SSet.yonedaEquiv s.2, scaffoldUnderChain s.1))
    (underWeightedColimitToReplacement_ι F (s.1.obj 0))
  calc
    _ = (simplicialReplacementUnderEvaluation F (s.1.obj 0)).app (Opposite.op ⦋n⦌)
        (scaffoldUnderChain s.1, SSet.yonedaEquiv s.2) := h
    _ = ⟨s.1, SSet.yonedaEquiv.symm (SSet.yonedaEquiv s.2)⟩ :=
      simplicialReplacementUnderEvaluation_scaffold F s.1 (SSet.yonedaEquiv s.2)
    _ = s := by
      rcases s with ⟨σ, x⟩
      simp only [Equiv.symm_apply_apply]

/-- 元の coend の全生成元での正規化により、比較の左逆も同じ点の公式になる。 -/
lemma replacementUnderWeightedPoint_leftInverse (F : I ⥤ SSet.{u}) (n : ℕ) :
    Function.LeftInverse (replacementUnderWeightedPoint F n)
      ((underWeightedColimitToReplacement F).app (Opposite.op ⦋n⦌)) := by
  have h : (fun z => replacementUnderWeightedPoint F n
      ((underWeightedColimitToReplacement F).app (Opposite.op ⦋n⦌) z)) = id := by
    apply weightedColimitDegree_hom_ext (underNerveWeight I) F (Opposite.op ⦋n⦌)
    intro i s
    rcases s with ⟨x, τ⟩
    have hv := congrArg (fun g => g.app (Opposite.op ⦋n⦌) (x, τ))
      (underWeightedColimitToReplacement_ι F i)
    change (underWeightedColimitToReplacement F).app (Opposite.op ⦋n⦌)
      ((weightedColimitι (underNerveWeight I) F i).app (Opposite.op ⦋n⦌) (x, τ)) =
        (simplicialReplacementUnderEvaluation F i).app (Opposite.op ⦋n⦌) (τ, x) at hv
    rw [hv]
    change (weightedColimitι (underNerveWeight I) F (τ.obj 0).right).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (SSet.yonedaEquiv.symm x ≫ F.map (τ.obj 0).hom),
        scaffoldUnderChain (τ ⋙ Under.forget i)) = _
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact underWeightedColimit_normalize F τ x
  exact congrFun h

/-- 既に構成した大域の自然比較射は同型。新しい成分同型の族から射を作らない。 -/
instance underWeightedColimitToReplacement_isIso (F : I ⥤ SSet.{u}) :
    IsIso (underWeightedColimitToReplacement F) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨⟨n⟩⟩
  apply (isIso_iff_bijective _).mpr
  exact ⟨(replacementUnderWeightedPoint_leftInverse F n).injective,
    (replacementUnderWeightedPoint_rightInverse F n).surjective⟩

/-- 同じ指定自然比較を順方向とする、既存二模型の同型。 -/
def underWeightedColimitReplacementIso (F : I ⥤ SSet.{u}) :
    weightedColimit (underNerveWeight I) F ≅ simplicialReplacement F :=
  asIso (underWeightedColimitToReplacement F)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
