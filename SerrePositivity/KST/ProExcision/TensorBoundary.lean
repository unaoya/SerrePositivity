module

public import SerrePositivity.KST.ProExcision.KoszulGraded
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomogeneous

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 次数ごと分裂する短完全列のテンソル境界

概要：全テンソル後の境界に、係数複体の微分が余分な項を残さないことを示す。
方針：純テンソルに評価し、分裂の切断と引き戻しの合成が零であることを使う。
規約：分裂は次数ごとでよく、複体の分裂は仮定しない。
使われ方：KST Lemma 4.10 の初頁微分と Koszul 微分の比較。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

variable {R : Type u} [CommRing R]

/-- 概要：次数ごとのテンソル写像を同次の純テンソルに評価する。
方針：全テンソルへの包含との可換式を評価する。
規約：入力写像に複体射の条件は不要。使われ方：KST Lemma 4.10 の境界計算。 -/
theorem tensorDegreeMap_apply_homogeneous
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : ∀ i, P.X i ⟶ P'.X i) (g : ∀ j, Q.X j ⟶ Q'.X j)
    (i j n : ℤ) (h : i + j = n) (x : P.X i) (y : Q.X j) :
    (cochainTensorDegreeMap f g n)
      (ιTensorObj P Q i j n h (x ⊗ₜ[R] y)) =
        ιTensorObj P' Q' i j n h (f i x ⊗ₜ[R] g j y) :=
  congrArg (fun k ↦ k.hom (x ⊗ₜ[R] y)) (ι_cochainTensorDegreeMap f g i j n h)

/-- 概要：テンソルした短完全列の境界は、元の境界だけを純テンソルに作用させる。
方針：全微分を二項に展開し、係数複体の微分の項を分裂の s≫r=0 で消す。
規約：任意の次数ごと分裂する短複体と任意の係数複体。
使われ方：KST Lemma 4.10 の補助初頁の微分。 -/
theorem tensorSplitBoundary_apply_homogeneous
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j n : ℤ) (h : i + j = n) (x : S.X₃.X i) (y : K.X j) :
    ((CochainComplex.cocycleOfDegreewiseSplit (cochainTensorShortComplexRight S K)
      (cochainTensorShortComplexRightSplitting S σ K)).1.v n (n + 1) rfl)
        (ιTensorObj S.X₃ K i j n h (x ⊗ₜ[R] y)) =
      ιTensorObj S.X₁ K (i + 1) j (n + 1) (by omega)
        (((σ (i + 1)).r (S.X₂.d i (i + 1) ((σ i).s x))) ⊗ₜ[R] y) := by
  change (cochainTensorDegreeMap (fun k ↦ (σ k).r) (fun k ↦ 𝟙 (K.X k)) (n + 1))
    ((cochainTensor S.X₂ K).d n (n + 1)
      ((cochainTensorDegreeMap (fun k ↦ (σ k).s) (fun k ↦ 𝟙 (K.X k)) n)
        (ιTensorObj S.X₃ K i j n h (x ⊗ₜ[R] y)))) = _
  rw [tensorDegreeMap_apply_homogeneous, cochainTensor_d_apply_ι, map_add, Units.smul_def, map_zsmul,
    tensorDegreeMap_apply_homogeneous, tensorDegreeMap_apply_homogeneous]
  have hz : (σ i).r ((σ i).s x) = 0 :=
    congrArg (fun k ↦ k.hom x) (σ i).s_r
  simp only [ModuleCat.id_apply]
  erw [hz]
  simp

end SerrePositivity.KST.ProExcision
