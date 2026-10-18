module

public import SerrePositivity.KST.ProExcision.CoefficientHomology
public import SerrePositivity.KST.ProExcision.TensorGradeBoundary

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 一項テンソル比較の係数自然性

概要：一項複体との全テンソルをシフトした通常のテンソルへ比較する同型は係数射に自然。
方針：次数零の逆比較を同次包含で検証し、標準シフト比較と合成する。
規約：複体レベルの比較には平坦性を使わない。
使われ方：KST Lemma 4.10 の初頁微分のホモロジー比較。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：次数零の一項テンソル比較の逆射は係数射に自然。
方針：各次数の唯一の同次包含を追い、一項複体射の成分を使う。
規約：平坦性は不要。使われ方：KST Lemma 4.10 の係数自然性の基本計算。 -/
theorem singleZeroTensorIso_inv_naturality
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((((curriedTensor (ModuleCat.{u} R)).map f).mapHomologicalComplex (.up ℤ)).app K) ≫
      (cochainTensorSingleLeftIso N K).inv =
      (cochainTensorSingleLeftIso M K).inv ≫
        cochainTensorMap ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map f) (𝟙 K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (f ▷ K.X n) ≫ ((singleObjXSelf (.up ℤ) 0 N).inv ▷ K.X n) ≫
      ιTensorObj (cochainSingleZero N) K 0 n n (zero_add n) =
    ((singleObjXSelf (.up ℤ) 0 M).inv ▷ K.X n) ≫
      ιTensorObj (cochainSingleZero M) K 0 n n (zero_add n) ≫
        (cochainTensorMap ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map f) (𝟙 K)).f n
  rw [ιTensorObj_cochainTensorMap]
  simp only [HomologicalComplex.id_f, tensorHom_id]
  erw [single_map_f_self]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id_assoc]

/-- 概要：次数零の一項テンソル比較の正射は係数射に自然。
方針：逆比較の自然性を二つの同型で相殺する。
規約：同じ標準比較を使う。使われ方：KST Lemma 4.10 のシフトつき比較の合成。 -/
theorem singleZeroTensorIso_hom_naturality
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorMap ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map f) (𝟙 K) ≫
      (cochainTensorSingleLeftIso N K).hom =
      (cochainTensorSingleLeftIso M K).hom ≫
        ((((curriedTensor (ModuleCat.{u} R)).map f).mapHomologicalComplex (.up ℤ)).app K) := by
  apply (cancel_epi (cochainTensorSingleLeftIso M K).inv).mp
  rw [← Category.assoc, ← singleZeroTensorIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- 概要：任意次数の一項テンソルのシフト比較は係数射に自然。
方針：一項複体のシフト同型、全テンソルの左シフト同型、次数零の比較の自然性を合成する。
規約：シフトは -a、係数射に平坦性は不要。
使われ方：KST Lemma 4.10 の初頁の係数ホモロジーと微分の比較。 -/
theorem singleTensorShiftIso_coefficient
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    cochainTensorMap ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).map f) (𝟙 K) ≫
      (singleTensorShiftIso N K a).hom =
      (singleTensorShiftIso M K a).hom ≫
        ((((curriedTensor (ModuleCat.{u} R)).map f).mapHomologicalComplex (.up ℤ)).app K)⟦-a⟧' := by
  let F := cochainTensorFixedRight K
  let shift := shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-a)
  let α := ((CochainComplex.singleFunctors (ModuleCat.{u} R)).shiftIso (-a) a 0 (by omega)).inv
  let z := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map f
  let w := (CochainComplex.singleFunctor (ModuleCat.{u} R) a).map f
  let tM := (cochainTensorShiftLeft (cochainSingleZero M) K (-a)).hom
  let tN := (cochainTensorShiftLeft (cochainSingleZero N) K (-a)).hom
  let uM := shift.map (cochainTensorSingleLeftIso M K).hom
  let uN := shift.map (cochainTensorSingleLeftIso N K).hom
  let τ := (((curriedTensor (ModuleCat.{u} R)).map f).mapHomologicalComplex (.up ℤ)).app K
  have hE : F.map w ≫ F.map (α.app N) = F.map (α.app M) ≫ F.map (shift.map z) := by
    rw [← F.map_comp, α.naturality f, F.map_comp]
    rfl
  have hT : F.map (shift.map z) ≫ tN = tM ≫ shift.map (F.map z) :=
    cochainTensorShiftLeft_naturality (Q := K) z (-a)
  have hU : shift.map (F.map z) ≫ uN = uM ≫ shift.map τ := by
    have h := congrArg shift.map (singleZeroTensorIso_hom_naturality f K)
    rw [shift.map_comp, shift.map_comp] at h
    exact h
  change F.map w ≫ (F.map (α.app N) ≫ tN ≫ uN) =
    (F.map (α.app M) ≫ tM ≫ uM) ≫ shift.map τ
  calc
    _ = (F.map w ≫ F.map (α.app N)) ≫ tN ≫ uN := by simp only [Category.assoc]
    _ = (F.map (α.app M) ≫ F.map (shift.map z)) ≫ tN ≫ uN := by rw [hE]
    _ = F.map (α.app M) ≫ (F.map (shift.map z) ≫ tN) ≫ uN := by
      simp only [Category.assoc]
    _ = F.map (α.app M) ≫ (tM ≫ shift.map (F.map z)) ≫ uN := by rw [hT]
    _ = F.map (α.app M) ≫ tM ≫ (shift.map (F.map z) ≫ uN) := by
      simp only [Category.assoc]
    _ = F.map (α.app M) ≫ tM ≫ (uM ≫ shift.map τ) := by rw [hU]
    _ = _ := by simp only [Category.assoc]

/-- 概要：一項テンソルのホモロジー比較は平坦係数間の射に自然。
方針：一項テンソルのシフト比較、ホモロジーのシフト比較、平坦係数比較の自然性を合成する。
規約：両係数を平坦とし、ホモロジー次数は q-a。
使われ方：KST Lemma 4.10 の補助初頁微分の係数写像。 -/
theorem singleTensorHomologyIso_coefficient
    {M N : ModuleCat.{u} R} [Module.Flat R M] [Module.Flat R N]
    (f : M ⟶ N) (K : CochainComplex (ModuleCat.{u} R) ℤ) (a q : ℤ) :
    homologyMap (cochainTensorMap
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).map f) (𝟙 K)) q ≫
      (singleTensorHomologyIso N K a q).hom =
      (singleTensorHomologyIso M K a q).hom ≫ (f ▷ K.homology (q - a)) := by
  let A := ((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K
  let B := ((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj K
  let τ := (((curriedTensor (ModuleCat.{u} R)).map f).mapHomologicalComplex (.up ℤ)).app K
  let t := homologyMap (cochainTensorMap
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).map f) (𝟙 K)) q
  let eM := homologyMap (singleTensorShiftIso M K a).hom q
  let eN := homologyMap (singleTensorShiftIso N K a).hom q
  let S := CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R) (-a) q (q - a) (by omega)
  let lM := (flatLeftTensorHomologyIso M (q - a)).hom.app K
  let lN := (flatLeftTensorHomologyIso N (q - a)).hom.app K
  have hE : t ≫ eN = eM ≫ homologyMap (τ⟦-a⟧') q := by
    have h := congrArg (fun f ↦ (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map f)
      (singleTensorShiftIso_coefficient f K a)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hS : homologyMap (τ⟦-a⟧') q ≫ S.hom.app B =
      S.hom.app A ≫ homologyMap τ (q - a) := S.hom.naturality τ
  have hL : homologyMap τ (q - a) ≫ lN = lM ≫ (f ▷ K.homology (q - a)) :=
    flatLeftTensorHomologyIso_map f K (q - a)
  change t ≫ (eN ≫ S.hom.app B ≫ lN) =
    (eM ≫ S.hom.app A ≫ lM) ≫ (f ▷ K.homology (q - a))
  calc
    _ = (t ≫ eN) ≫ S.hom.app B ≫ lN := by simp only [Category.assoc]
    _ = (eM ≫ homologyMap (τ⟦-a⟧') q) ≫ S.hom.app B ≫ lN := by rw [hE]
    _ = eM ≫ (homologyMap (τ⟦-a⟧') q ≫ S.hom.app B) ≫ lN := by
      simp only [Category.assoc]
    _ = eM ≫ (S.hom.app A ≫ homologyMap τ (q - a)) ≫ lN := by rw [hS]
    _ = eM ≫ S.hom.app A ≫ (homologyMap τ (q - a) ≫ lN) := by
      simp only [Category.assoc]
    _ = eM ≫ S.hom.app A ≫ (lM ≫ (f ▷ K.homology (q - a))) := by rw [hL]
    _ = _ := by simp only [Category.assoc]

end SerrePositivity.KST.ProExcision
