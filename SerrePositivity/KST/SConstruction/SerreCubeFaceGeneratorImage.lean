module
public import SerrePositivity.KST.SConstruction.SerreCubeFaceGeneratorIndex

/-! # 元の標準面最高生成元像と一端点 tensor 生成元
概要：元の全座標の標準面最高生成元像を、同じ一端点 tensor 添字の元へ戻す。
方針：元の右端面と内側面の tensor 評価を、元の次数移送付き生成元表示で帰納する。
規約：元の鎖射と次数移送を保持。使われ方：任意の HA 線形復元の全面像評価。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右端標準面の最高生成元像は、元の右端だけを端点にした生成元。 -/
lemma serreCubeFace_zero_top_generator (b : Bool) (n : ℕ) :
    (serreCubeFace A b n 0).hom.f (-(n : ℤ)) (serreCubeTopCell A n) =
      eqToHom (congrArg (fun k => (serreCubeComplex A (n + 1)).X k)
        (serreCubeFaceGeneratorIndex_degree b n 0))
          (serreCubeGenerator A (n + 1) (serreCubeFaceGeneratorIndex b n 0)) := by
  have h := serreCubeGenerator_point_cast A b n (serreCubeTopGeneratorIndex n)
    (-(n : ℤ)) (serreCubeTopGeneratorIndex_degree n)
  have ht := congrArg (fun w => (serreCubeFace A b n 0).hom.f (-(n : ℤ)) w)
    (serreCubeTopGeneratorIndex_cast A n)
  cases n <;> exact ht.symm.trans h

/-- 元の全座標の標準面最高生成元像は、同じ元の一端点 tensor 生成元の次数移送。 -/
lemma serreCubeFace_top_generator (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeFace A b n i).hom.f (-(n : ℤ)) (serreCubeTopCell A n) =
      eqToHom (congrArg (fun k => (serreCubeComplex A (n + 1)).X k)
        (serreCubeFaceGeneratorIndex_degree b n i))
          (serreCubeGenerator A (n + 1) (serreCubeFaceGeneratorIndex b n i)) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by have hi := i.isLt; omega)
    subst i
    exact serreCubeFace_zero_top_generator A b 0
  | succ n ih =>
    refine Fin.cases (serreCubeFace_zero_top_generator A b (n + 1)) (fun j => ?_) i
    have h := serreCubeFace_succ_apply A b n j (-(n : ℤ)) (-1)
      (-((n + 1 : ℕ) : ℤ)) (by omega) (serreCubeTopCell A n) (serreIntervalEdge A)
    have ht := congrArg (fun w => ιTensorObj (serreCubeComplex A (n + 1)) (serreInterval A)
      (-(n : ℤ)) (-1) (-((n + 1 : ℕ) : ℤ)) (by omega) (w ⊗ₜ[A] serreIntervalEdge A)) (ih j)
    exact h.trans (ht.trans (serreCubeGenerator_keep_cast A (n + 1)
      (serreCubeFaceGeneratorIndex b n j) (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ))
        (serreCubeFaceGeneratorIndex_degree b n j) (by omega)))

end SerrePositivity.KST.SConstruction
