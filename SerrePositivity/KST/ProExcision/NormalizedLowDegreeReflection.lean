module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedStrictification
public import Mathlib.AlgebraicTopology.DoldKan.Decomposition

/-!
# 正規化した低次数の一致の反映

概要：正規化した射が次数≤m で一致すれば、元の単体的射も同じ次数で一致する。
方針：Moore 射影の像の一致と、補射影 Q の一つ低い次数を通る退化分解を使う。
規約：KST Construction A.5、非被約零次を含む。全体の忠実性だけを低次数へ誤用しない。
使われ方：復元した実区間射の次数制限つき両端条件。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {X Y : SimplicialObject A}

/-- 概要：正規化した一つの次数の一致は Moore 射影の後の二射の一致を与える。
方針：PInfty を Moore 射影と包含の合成へ分解し、包含の自然性を使う。
規約：KST A.5。使われ方：低次数の一致の帰納法の正規化部分。 -/
lemma normalizedMap_component_eq_projection (f g : X ⟶ Y) (n : ℕ)
    (h : ((normalizedMooreComplex A).map f).f n = ((normalizedMooreComplex A).map g).f n) :
    (P (X := X) n).f n ≫ f.app (op ⦋n⦌) = (P (X := X) n).f n ≫ g.app (op ⦋n⦌) := by
  have hp := congrArg (fun k ↦ k.f n)
    (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X)
  change (PInftyToNormalizedMooreComplex X).f n ≫ (inclusionOfMooreComplexMap X).f n =
    (PInfty (X := X)).f n at hp
  have hp' : (P (X := X) n).f n =
      (PInftyToNormalizedMooreComplex X).f n ≫ (inclusionOfMooreComplexMap X).f n := by
    simpa only [PInfty_f] using hp.symm
  have hf := congrArg (fun k ↦ k.f n) ((inclusionOfMooreComplex A).naturality f)
  have hg := congrArg (fun k ↦ k.f n) ((inclusionOfMooreComplex A).naturality g)
  change ((normalizedMooreComplex A).map f).f n ≫ (inclusionOfMooreComplexMap Y).f n =
    (inclusionOfMooreComplexMap X).f n ≫ f.app (op ⦋n⦌) at hf
  change ((normalizedMooreComplex A).map g).f n ≫ (inclusionOfMooreComplexMap Y).f n =
    (inclusionOfMooreComplexMap X).f n ≫ g.app (op ⦋n⦌) at hg
  rw [hp', Category.assoc, ← hf, h, hg, ← Category.assoc]

/-- 概要：一つ低い次数で二射が一致すれば Q の退化部分の後でも一致する。
方針：Q の各項の最後の退化写像に自然性を使い、低い次数へ戻す。
規約：KST A.5。使われ方：低次数の一致の帰納法の退化部分。 -/
lemma simplicialMap_eq_complement_of_prev (f g : X ⟶ Y) (n : ℕ)
    (h : f.app (op ⦋n⦌) = g.app (op ⦋n⦌)) :
    (Q (X := X) (n + 1)).f (n + 1) ≫ f.app (op ⦋n + 1⦌) =
      (Q (X := X) (n + 1)).f (n + 1) ≫ g.app (op ⦋n + 1⦌) := by
  rw [decomposition_Q]
  simp only [Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i _
  have hf : X.σ i.rev ≫ f.app (op ⦋n + 1⦌) = f.app (op ⦋n⦌) ≫ Y.σ i.rev :=
    f.naturality (SimplexCategory.σ i.rev).op
  have hg : X.σ i.rev ≫ g.app (op ⦋n + 1⦌) = g.app (op ⦋n⦌) ≫ Y.σ i.rev :=
    g.naturality (SimplexCategory.σ i.rev).op
  rw [hf, hg, h]

/-- 概要：正規化した二射の次数≤m の一致は元の単体的射の同じ範囲の一致を与える。
方針：次数に関する帰納法で P 部分と Q の退化部分の一致を足す。
規約：KST Construction A.5、零次は Moore 射影が恒等であることを使う。
使われ方：低次の鎖比較から実 m 次区間ホモトピーへの復元。 -/
theorem normalizedMap_eq_low_reflect (f g : X ⟶ Y) (m : ℕ)
    (h : ∀ n, n ≤ m → ((normalizedMooreComplex A).map f).f n =
      ((normalizedMooreComplex A).map g).f n) (n : ℕ) (hn : n ≤ m) :
    f.app (op ⦋n⦌) = g.app (op ⦋n⦌) := by
  induction n with
  | zero =>
    have hp := normalizedMap_component_eq_projection f g 0 (h 0 hn)
    simpa only [P_f_0_eq, Category.id_comp] using hp
  | succ n ih =>
    have hp := normalizedMap_component_eq_projection f g (n + 1) (h (n + 1) hn)
    have hq := simplicialMap_eq_complement_of_prev f g n (ih (by omega))
    calc
      _ = ((P (X := X) (n + 1)).f (n + 1) + (Q (X := X) (n + 1)).f (n + 1)) ≫
          f.app (op ⦋n + 1⦌) := by
        rw [P_add_Q_f]
        exact (Category.id_comp _).symm
      _ = (P (X := X) (n + 1)).f (n + 1) ≫ f.app (op ⦋n + 1⦌) +
          (Q (X := X) (n + 1)).f (n + 1) ≫ f.app (op ⦋n + 1⦌) := by rw [Preadditive.add_comp]
      _ = (P (X := X) (n + 1)).f (n + 1) ≫ g.app (op ⦋n + 1⦌) +
          (Q (X := X) (n + 1)).f (n + 1) ≫ g.app (op ⦋n + 1⦌) := by rw [hp, hq]
      _ = _ := by
        rw [← Preadditive.add_comp, P_add_Q_f]
        exact Category.id_comp _

end SerrePositivity.KST.ProExcision
