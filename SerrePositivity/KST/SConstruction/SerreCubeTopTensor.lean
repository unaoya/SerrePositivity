module
public import SerrePositivity.KST.SConstruction.SerreCubeTopCell
public import SerrePositivity.KST.SConstruction.SerreCubeTensorHomValues
public import SerrePositivity.KST.SConstruction.ComonoidStructureMaps
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! # 元の Serre tensor 分割での最高生成元の像
概要：元の n+m 次元の最高生成元は、元の tensor 比較で両ブロックの最高生成元に写る。
方針：同じ比較の元の右単位・結合替えの再帰を、元の全辺 tensor 上で評価する。
規約：座標反転や符号の置換を加えない。使われ方：HA の分割合成項の具体化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の零右ブロックの tensor 比較の基礎の chain map は、同じ逆右単位射。 -/
lemma serreCubeTensorIso_zero_chain (n : ℕ) :
    (serreCubeTensorIso A n 0).hom.hom = (ρ_ (serreCubeComplex A n)).inv :=
  (congrArg (fun e => e.hom.hom) (serreCubeTensorIso_zero A n)).trans
    (comonoidRightUnitorInvHom (serreCubeComonoid A n))

/-- 元の一段の tensor 比較の基礎の chain map は、同じ tensor と結合替えの合成。 -/
lemma serreCubeTensorIso_succ_chain (n m : ℕ) :
    (serreCubeTensorIso A n (m + 1)).hom.hom =
      ((serreCubeTensorIso A n m).hom.hom ⊗ₘ 𝟙 (serreInterval A)) ≫
        (α_ (serreCubeComplex A n) (serreCubeComplex A m) (serreInterval A)).hom := by
  have h := congrArg (fun f => f.hom) (serreCubeTensorIso_succ_hom A n m)
  exact h.trans (by
    simp only [Comon.comp_hom', Comon.monoidal_tensorHom_hom, Comon.id_hom',
      comonoidAssociatorHom]
    rfl)

/-- 元の実 tensor 比較は、元の全辺 tensor の最高生成元を同じ二ブロックへ厳密に分割する。 -/
lemma serreCubeTopCell_tensor (p q : ℕ) :
    (serreCubeTensorIso A p q).hom.hom.f (-((p + q : ℕ) : ℤ)) (serreCubeTopCell A (p + q)) =
      ιTensorObj (serreCubeComplex A p) (serreCubeComplex A q)
        (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)
        (serreCubeTopCell A p ⊗ₜ[A] serreCubeTopCell A q) := by
  induction q with
  | zero =>
    exact (congrArg (fun f => f.f (-(p : ℤ)) (serreCubeTopCell A p))
      (serreCubeTensorIso_zero_chain A p)).trans
        (complexRightUnitor_inv_apply (serreCubeComplex A p) (-(p : ℤ)) (serreCubeTopCell A p))
  | succ q ih =>
    have h := congrArg (fun f => f.f (-((p + (q + 1) : ℕ) : ℤ))
      (serreCubeTopCell A (p + (q + 1)))) (serreCubeTensorIso_succ_chain A p q)
    have ht := tensorMap_apply (serreCubeTensorIso A p q).hom.hom (𝟙 (serreInterval A))
      (-((p + q : ℕ) : ℤ)) (-1) (-((p + (q + 1) : ℕ) : ℤ)) (by omega)
      (serreCubeTopCell A (p + q)) (serreIntervalEdge A)
    have hi := congrArg (fun z =>
      ιTensorObj (serreCubeComplex A p ⊗ serreCubeComplex A q) (serreInterval A)
        (-((p + q : ℕ) : ℤ)) (-1) (-((p + (q + 1) : ℕ) : ℤ)) (by omega)
        (z ⊗ₜ[A] serreIntervalEdge A)) ih
    exact h.trans ((chain_comp_apply _ _ _ _).trans
      ((congrArg (fun z => (α_ (serreCubeComplex A p) (serreCubeComplex A q)
        (serreInterval A)).hom.f (-((p + (q + 1) : ℕ) : ℤ)) z) (ht.trans hi)).trans
          (associator_apply_of_sums (serreCubeComplex A p) (serreCubeComplex A q)
            (serreInterval A) (-(p : ℤ)) (-(q : ℤ)) (-1) (-((p + q : ℕ) : ℤ))
            (-((q + 1 : ℕ) : ℤ)) (-((p + (q + 1) : ℕ) : ℤ)) (by omega) (by omega)
            (by omega) (serreCubeTopCell A p) (serreCubeTopCell A q) (serreIntervalEdge A))))

end SerrePositivity.KST.SConstruction
