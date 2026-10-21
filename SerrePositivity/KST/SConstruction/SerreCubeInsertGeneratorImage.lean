module
public import SerrePositivity.KST.SConstruction.SerreCubeInsertGeneratorIndex
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorPointValues

/-! # 元の任意の生成元上の全座標の実標準面像
概要：元の標準面を任意の生成元に適用した像を、同じ端点挿入添字の元で回収する。
方針：元の右端面の評価と内側面の斉次 tensor 評価を帰納する。
規約：元の実面射・次数移送を保持。使われ方：全次数の面制限と source 微分の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の左生成元の次数移送を含む tensor は、元の次の生成元を回収する。 -/
lemma serreCubeGenerator_succ_left_cast (n : ℕ) (i : SerreCubeGeneratorIndex n) (j : Fin 3)
    (p k : ℤ) (hp : serreCubeGeneratorDegree n i = p)
    (hk : p + serreIntervalGeneratorDegree j = k) :
    ιTensorObj (serreCubeComplex A n) (serreInterval A) p (serreIntervalGeneratorDegree j) k hk
      (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hp)
        (serreCubeGenerator A n i) ⊗ₜ[A] serreIntervalGenerator A j) =
      eqToHom (congrArg (fun d => (serreCubeComplex A (n + 1)).X d)
        ((congrArg (· + serreIntervalGeneratorDegree j) hp).trans hk))
        (serreCubeGenerator A (n + 1) (i, j)) := by
  cases hp
  exact (serreCubeGenerator_succ_cast A n i j k hk).symm

/-- 元の全座標の標準面像は、元の同じ端点挿入生成元の次数移送。 -/
lemma serreCubeFace_generator (b : Bool) (n : ℕ) (q : Fin (n + 1))
    (i : SerreCubeGeneratorIndex n) :
    (serreCubeFace A b n q).hom.f (serreCubeGeneratorDegree n i) (serreCubeGenerator A n i) =
      eqToHom (congrArg (fun d => (serreCubeComplex A (n + 1)).X d)
        (serreCubeInsertGeneratorIndex_degree b n q i))
        (serreCubeGenerator A (n + 1) (serreCubeInsertGeneratorIndex b n q i)) := by
  induction n with
  | zero =>
    have hq : q = 0 := Fin.ext (by have hq := q.isLt; omega)
    subst q
    exact serreCubeGenerator_point_cast A b 0 i _ rfl
  | succ n ih =>
    obtain ⟨i, j⟩ := i
    refine Fin.cases ?_ (fun q => ?_) q
    · exact serreCubeGenerator_point_cast A b (n + 1) (i, j) _ rfl
    · have h := serreCubeFace_succ_apply A b n q (serreCubeGeneratorDegree n i)
        (serreIntervalGeneratorDegree j) (serreCubeGeneratorDegree (n + 1) (i, j)) rfl
        (serreCubeGenerator A n i) (serreIntervalGenerator A j)
      have ht := congrArg (fun x => ιTensorObj (serreCubeComplex A (n + 1)) (serreInterval A)
        (serreCubeGeneratorDegree n i) (serreIntervalGeneratorDegree j)
        (serreCubeGeneratorDegree (n + 1) (i, j)) rfl
        (x ⊗ₜ[A] serreIntervalGenerator A j)) (ih q i)
      exact h.trans (ht.trans (serreCubeGenerator_succ_left_cast A (n + 1)
        (serreCubeInsertGeneratorIndex b n q i) j _ _
        (serreCubeInsertGeneratorIndex_degree b n q i) rfl))

/-- 元の任意指定次数でも、全座標の面像は同じ端点挿入生成元を回収する。 -/
lemma serreCubeFace_generator_cast (b : Bool) (n : ℕ) (q : Fin (n + 1))
    (i : SerreCubeGeneratorIndex n) (k : ℤ) (hi : serreCubeGeneratorDegree n i = k) :
    (serreCubeFace A b n q).hom.f k
      (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hi)
        (serreCubeGenerator A n i)) =
      eqToHom (congrArg (fun d => (serreCubeComplex A (n + 1)).X d)
        ((serreCubeInsertGeneratorIndex_degree b n q i).trans hi))
        (serreCubeGenerator A (n + 1) (serreCubeInsertGeneratorIndex b n q i)) := by
  cases hi
  exact serreCubeFace_generator A b n q i

end SerrePositivity.KST.SConstruction
