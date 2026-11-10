module
public import SerrePositivity.KST.ProExcision.NormalizedChainHomotopyReconstruction
public import SerrePositivity.KST.ProExcision.NormalizedLowDegreeReflection

/-!
# 二つの低次一致する鎖比較から実 m 次ホモトピーへの復元

概要：二つの全鎖ホモトピーの比較先が低次で一致すれば、元の二射の実 m 次ホモトピーを作る。
方針：ホモトピーの差と第二の始点の恒等比較を足し、補正した終点を Dold–Kan で戻す。
規約：KST Construction A.5、比較先の低次一致だけを使い、区間ホモトピーの存在を仮定しない。
使われ方：正規化テンソルの augmentation 補正式と EZ 比較の合成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology
open scoped Simplicial
variable {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
variable {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D}
variable {R S : (normalizedMooreComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) ⟶ (normalizedMooreComplex _).obj D}

/-- 概要：二つの比較ホモトピーの差から第一の始点と補正した終点の全鎖ホモトピーを作る。
方針：第一比較に第二比較の負を足し、第二の始点の恒等比較を足す。
規約：KST A.5、補正終点は R−S+N(g)。
使われ方：R と S が低次で一致すると実 m 次ホモトピーを得る。 -/
def chainComparisonDifferenceHomotopy
    (H₁ : Homotopy ((normalizedMooreComplex _).map f) R)
    (H₂ : Homotopy ((normalizedMooreComplex _).map g) S) :
    Homotopy ((normalizedMooreComplex _).map f)
      (R - S + (normalizedMooreComplex _).map g) := by
  let h := (H₁.add (H₂.smul (-1 : ℤ))).add (Homotopy.refl ((normalizedMooreComplex _).map g))
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · simp only [neg_smul, one_smul]
    abel
  · simp only [neg_smul, one_smul]
    abel

/-- 概要：補正終点の復元は比較先が一致する低次数で指定した第二の射に一致。
方針：正規化後の R−S が低次で零となることを低次数の反映で戻す。
規約：KST A.5、非被約零次を含む。
使われ方：復元した全区間ホモトピーを m 次で第二の射に合わせる。 -/
lemma normalizedComparisonCorrectedMap_eq_low (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D)
    (R S : (normalizedMooreComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) ⟶ (normalizedMooreComplex _).obj D)
    (m : ℕ) (hRS : ∀ n, n ≤ m → R.f n = S.f n) (n : ℕ) (hn : n ≤ m) :
    (normalizedMapReconstruct (R - S + (normalizedMooreComplex _).map g)).app (op ⦋n⦌) =
      g.app (op ⦋n⦌) := by
  apply normalizedMap_eq_low_reflect _ g m _ n hn
  intro k hk
  rw [normalizedMapReconstruct_map, add_f_apply, sub_f_apply, hRS k hk]
  simp only [sub_self, zero_add]

/-- 概要：二つの比較先が低次で一致する全鎖比較から実 m 次区間ホモトピーを構成する。
方針：差の全ホモトピーを復元し、補正終点の低次一致で両端を合わせる。
規約：KST Construction A.5、非被約 C(H) を保持し追加の存在仮定を使わない。
使われ方：正規化した augmentation 補正式の実区間への移送。 -/
def linearizedMHomotopyOfChainComparisons
    (H₁ : Homotopy ((normalizedMooreComplex _).map f) R)
    (H₂ : Homotopy ((normalizedMooreComplex _).map g) S)
    (m : ℕ) (hRS : ∀ n, n ≤ m → R.f n = S.f n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g m := by
  let e := normalizedMapReconstruct (R - S + (normalizedMooreComplex _).map g)
  let hh := (chainComparisonDifferenceHomotopy H₁ H₂).trans
    (Homotopy.ofEq (normalizedMapReconstruct_map (R - S + (normalizedMooreComplex _).map g)).symm)
  let h := LinearizedHomotopy.ofNormalizedChainHomotopy hh
  refine { h := h.h, h₀ := ?_, h₁ := ?_ }
  · intro n _
    exact congrArg (fun t ↦ t.app (op ⦋n⦌)) h.h₀
  · intro n hn
    exact (congrArg (fun t ↦ t.app (op ⦋n⦌)) h.h₁).trans
      (normalizedComparisonCorrectedMap_eq_low g R S m hRS n hn)

end SerrePositivity.KST.ProExcision
