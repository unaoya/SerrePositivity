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
  rw [tensorDegreeMap_apply_homogeneous, cochainTensor_d_apply_ι, map_add,
    Units.smul_def, map_zsmul,
    tensorDegreeMap_apply_homogeneous, tensorDegreeMap_apply_homogeneous]
  have hz : (σ i).r ((σ i).s x) = 0 :=
    congrArg (fun k ↦ k.hom x) (σ i).s_r
  simp only [ModuleCat.id_apply]
  erw [hz]
  simp

/-- 概要：テンソル境界の同次成分は、元の短完全列の境界を右テンソルした写像。
方針：純テンソル上の計算から加群のテンソル積の外延性で射の等式を得る。
規約：係数複体の微分に由来する項は消えている。
使われ方：KST Lemma 4.10 の初頁微分の射としての同定。 -/
@[reassoc]
theorem tensorSplitBoundary_homogeneous
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i j n : ℤ) (h : i + j = n) :
    ιTensorObj S.X₃ K i j n h ≫
      (CochainComplex.cocycleOfDegreewiseSplit (cochainTensorShortComplexRight S K)
        (cochainTensorShortComplexRightSplitting S σ K)).1.v n (n + 1) rfl =
      (((σ i).s ≫ S.X₂.d i (i + 1) ≫ (σ (i + 1)).r) ▷ K.X j) ≫
        ιTensorObj S.X₁ K (i + 1) j (n + 1) (by omega) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact tensorSplitBoundary_apply_homogeneous S σ K i j n h x y

/-- 概要：全テンソル後の次数ごと分裂境界は、元の境界のテンソルと同じ。
方針：各同次成分で比較し、全テンソルの左シフト同型で標的を合わせる。
規約：左シフト比較には符号を加えない。使われ方：KST Lemma 4.10 の初頁微分。 -/
theorem tensorSplitBoundary_eq
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex.homOfDegreewiseSplit (cochainTensorShortComplexRight S K)
      (cochainTensorShortComplexRightSplitting S σ K) =
      cochainTensorMap (CochainComplex.homOfDegreewiseSplit S σ) (𝟙 K) ≫
        (cochainTensorShiftLeft S.X₁ K (1 : ℤ)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono
    (CochainComplex.shiftFunctorObjXIso (cochainTensor S.X₁ K) 1 n (n + 1) rfl).hom).mp
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [CochainComplex.homOfDegreewiseSplit_f, tensorSplitBoundary_homogeneous_assoc,
    ιTensorObj_cochainTensorMap_assoc, ιTensorObj_cochainTensorShiftLeft_assoc]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, CochainComplex.homOfDegreewiseSplit_f,
    CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cocycle.mk,
    CochainComplex.HomComplex.Cochain.mk_v, HomologicalComplex.id_f,
    tensorHom_id, Category.comp_id, Category.id_comp]
  erw [id_whiskerRight]
  erw [Category.comp_id]

end SerrePositivity.KST.ProExcision
