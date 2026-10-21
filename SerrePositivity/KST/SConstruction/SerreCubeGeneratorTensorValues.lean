module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorConcat
public import SerrePositivity.KST.SConstruction.SerreCubeInsertGeneratorImage
public import SerrePositivity.KST.SConstruction.SerreCubeTopTensor

/-! # 元の全生成元の実 tensor 比較による左右分割
概要：元の連結生成元は、元の実 tensor 同型で同じ左右生成元の tensor に写る。
方針：元の比較の右単位・結合替えの再帰を、全端点・辺の斉次生成元上で評価する。
規約：元の全因子・指定次数を保持。使われ方：内部一端点の実左右 tensor 制限。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の実 tensor 比較は、元の連結生成元を同じ左右生成元へ全指定次数で分割する。 -/
lemma serreCubeGeneratorConcat_tensor (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (m : ℕ) (j : SerreCubeGeneratorIndex m) (k : ℤ)
    (hk : serreCubeGeneratorDegree n i + serreCubeGeneratorDegree m j = k) :
    (serreCubeTensorIso A n m).hom.hom.f k
      (eqToHom (congrArg (fun d => (serreCubeComplex A (n + m)).X d)
        ((serreCubeGeneratorConcat_degree n i m j).trans hk))
        (serreCubeGenerator A (n + m) (serreCubeGeneratorConcat n i m j))) =
      ιTensorObj (serreCubeComplex A n) (serreCubeComplex A m)
        (serreCubeGeneratorDegree n i) (serreCubeGeneratorDegree m j) k hk
        (serreCubeGenerator A n i ⊗ₜ[A] serreCubeGenerator A m j) := by
  induction m generalizing k with
  | zero =>
    have hki : serreCubeGeneratorDegree n i = k := (add_zero _).symm.trans hk
    cases hki
    exact (congrArg (fun f => f.f _ (serreCubeGenerator A n i))
      (serreCubeTensorIso_zero_chain A n)).trans
        (complexRightUnitor_inv_apply (serreCubeComplex A n) _ (serreCubeGenerator A n i))
  | succ m ih =>
    obtain ⟨j, l⟩ := j
    let p := serreCubeGeneratorDegree n i
    let q := serreCubeGeneratorDegree m j
    let r := serreIntervalGeneratorDegree l
    change p + (q + r) = k at hk
    have hs := serreCubeGenerator_succ_left_cast A (n + m)
      (serreCubeGeneratorConcat n i m j) l (p + q) k
      (serreCubeGeneratorConcat_degree n i m j) (by omega)
    have h₀ := congrArg (fun x => (serreCubeTensorIso A n (m + 1)).hom.hom.f k x) hs.symm
    have h₁ := congrArg (fun f => f.f k
      (ιTensorObj (serreCubeComplex A (n + m)) (serreInterval A) (p + q) r k (by omega)
        (eqToHom (congrArg (fun d => (serreCubeComplex A (n + m)).X d)
          (serreCubeGeneratorConcat_degree n i m j))
          (serreCubeGenerator A (n + m) (serreCubeGeneratorConcat n i m j)) ⊗ₜ[A]
            serreIntervalGenerator A l))) (serreCubeTensorIso_succ_chain A n m)
    have h₂ := tensorMap_apply (serreCubeTensorIso A n m).hom.hom (𝟙 (serreInterval A))
      (p + q) r k (by omega)
      (eqToHom (congrArg (fun d => (serreCubeComplex A (n + m)).X d)
        (serreCubeGeneratorConcat_degree n i m j))
        (serreCubeGenerator A (n + m) (serreCubeGeneratorConcat n i m j)))
      (serreIntervalGenerator A l)
    have h₃ := congrArg (fun x => ιTensorObj (serreCubeComplex A n ⊗ serreCubeComplex A m)
      (serreInterval A) (p + q) r k (by omega) (x ⊗ₜ[A] serreIntervalGenerator A l))
      (ih j (p + q) rfl)
    exact h₀.trans (h₁.trans ((chain_comp_apply _ _ _ _).trans
      ((congrArg (fun x => (α_ (serreCubeComplex A n) (serreCubeComplex A m)
        (serreInterval A)).hom.f k x) (h₂.trans h₃)).trans
          (associator_apply_of_sums (serreCubeComplex A n) (serreCubeComplex A m)
            (serreInterval A) p q r (p + q) (q + r) k rfl rfl (by omega)
            (serreCubeGenerator A n i) (serreCubeGenerator A m j) (serreIntervalGenerator A l)))))

end SerrePositivity.KST.SConstruction
