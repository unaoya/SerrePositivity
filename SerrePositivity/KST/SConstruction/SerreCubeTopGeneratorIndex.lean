module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorFaces
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorPointValues

/-! # 元の全辺 tensor 生成元の添字
概要：全座標で辺を選ぶ元の添字と、その自由次元・cochain 次数を回収する。
方針：元の零次元添字と辺添字 2 を、同じ tensor の順に再帰する。
規約：元の全生成元族を変更しない。使われ方：HA 成分を復元する最高生成元の指定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

/-- 全座標で元の辺を選ぶ、元の最高生成元の添字。 -/
def serreCubeTopGeneratorIndex : (n : ℕ) → SerreCubeGeneratorIndex n
  | 0 => PUnit.unit
  | n + 1 => (serreCubeTopGeneratorIndex n, 2)

/-- 元の全辺添字の自由次元は、元の cube 次元そのもの。 -/
lemma serreCubeTopGeneratorIndex_freeDimension (n : ℕ) :
    serreCubeGeneratorFreeDimension n (serreCubeTopGeneratorIndex n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (· + 1) ih

/-- 元の全辺添字の cochain 次数は、元の cube 次元の負値。 -/
lemma serreCubeTopGeneratorIndex_degree (n : ℕ) :
    serreCubeGeneratorDegree n (serreCubeTopGeneratorIndex n) = -(n : ℤ) :=
  (serreCubeGeneratorDegree_freeDimension n (serreCubeTopGeneratorIndex n)).trans
    (congrArg (fun d : ℕ => -(d : ℤ)) (serreCubeTopGeneratorIndex_freeDimension n))

/-- 元の全辺 tensor 生成元を最高次数へ移すと、元の最高生成元そのもの。 -/
lemma serreCubeTopGeneratorIndex_cast (A : Type u) [CommRing A] (n : ℕ) :
    eqToHom (congrArg (fun k => (serreCubeComplex A n).X k)
      (serreCubeTopGeneratorIndex_degree n))
        (serreCubeGenerator A n (serreCubeTopGeneratorIndex n)) = serreCubeTopCell A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := serreCubeGenerator_keep_cast A n (serreCubeTopGeneratorIndex n)
      (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (serreCubeTopGeneratorIndex_degree n) (by omega)
    exact h.symm.trans (congrArg (fun w =>
      ιTensorObj (serreCubeComplex A n) (serreInterval A) (-(n : ℤ)) (-1)
        (-((n + 1 : ℕ) : ℤ)) (by omega) (w ⊗ₜ[A] serreIntervalEdge A)) ih)

end SerrePositivity.KST.SConstruction
