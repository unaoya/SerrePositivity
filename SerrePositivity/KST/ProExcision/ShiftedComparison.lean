module

public import SerrePositivity.KST.ProExcision.SingleShiftCoherence

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# シフトした境界比較とホモロジー

概要：二つのシフトを含む複体射の比較を、ホモロジーの次数間の比較へ移す。
方針：ShiftSequence のシフト合成公式を使い、追加の符号規約を導入しない。
規約：比較射の結合に標準のシフト加法同型を使う。
使われ方：KST Lemma 4.10 の一項テンソル境界のホモロジー計算。
-/

universe u v w

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

/-- 概要：シフト加法同型で結合した二つの射の比較は、シフト列の誘導射の比較を与える。
方針：シフト同型とシフト写像の合成公式で左辺を一つの誘導射へまとめる。
規約：任意の整数シフト列。使われ方：KST Lemma 4.10 の境界比較をホモロジーへ移す。 -/
theorem shiftMap_comparison
    {C : Type v} [Category C] [HasShift C ℤ] {D : Type w} [Category D]
    (F : C ⥤ D) [F.ShiftSequence ℤ] {X Y A B : C}
    (n m mn : ℤ) (hnm : m + n = mn)
    (f : X ⟶ Y⟦n⟧) (g : Y ⟶ B⟦m⟧) (u : X ⟶ A⟦mn⟧) (τ : A ⟶ B)
    (h : f ≫ g⟦n⟧' ≫ (shiftFunctorAdd' C m n mn hnm).inv.app B = u ≫ τ⟦mn⟧')
    (q q' s : ℤ) (hq : n + q = q') (hs : m + q' = s) :
    F.shiftMap f q q' hq ≫ F.shiftMap g q' s hs =
      F.shiftMap u q s (by omega) ≫ (F.shift s).map τ := by
  calc
    _ = F.shiftMap (f ≫ g⟦n⟧' ≫ (shiftFunctorAdd' C m n mn hnm).inv.app B)
        q s (by omega) := by
      rw [Functor.shiftMap, Category.assoc,
        F.shiftIso_hom_app_comp_shiftMap g n mn hnm q q' s hq hs]
      simp only [Functor.shiftMap, Functor.map_comp, Category.assoc]
    _ = F.shiftMap (u ≫ τ⟦mn⟧') q s (by omega) :=
      congrArg (fun f ↦ F.shiftMap f q s (by omega)) h
    _ = _ := F.shiftMap_comp u τ q s (by omega)

variable {R : Type u} [CommRing R]

/-- 概要：一項テンソル境界のホモロジー誘導射は、標準正規化の後では通常の係数射になる。
方針：複体射のシフト境界比較を、ホモロジー関手のシフト列へ適用する。
規約：源の次数は q、境界の標的は q+1、係数の次数は q-a。
使われ方：KST Lemma 4.10 の初頁微分のホモロジー比較。 -/
theorem tensorSingleHomology_shift_boundary
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a q : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (tensorSingleDegreeBoundary f K a) q (q + 1) (by omega) ≫
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (singleTensorShiftIso N K (a + 1)).hom (q + 1) (q - a) (by omega) =
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (singleTensorShiftIso M K a).hom q (q - a) (by omega) ≫
      homologyMap
        ((((curriedTensor (ModuleCat.{u} R)).map f).mapHomologicalComplex (.up ℤ)).app K) (q - a) :=
  shiftMap_comparison (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0)
    1 (-(a + 1)) (-a) (by omega) (tensorSingleDegreeBoundary f K a)
    (singleTensorShiftIso N K (a + 1)).hom (singleTensorShiftIso M K a).hom
    ((((curriedTensor (ModuleCat.{u} R)).map f).mapHomologicalComplex (.up ℤ)).app K)
    (tensorSingleShift_boundary f K a) q (q + 1) (q - a) (by omega) (by omega)

/-- 概要：平坦係数の一項境界は、ホモロジー比較後に係数射と H(K) のテンソルになる。
方針：シフト境界のホモロジー比較に、平坦係数比較の自然性を後合成する。
規約：両係数は平坦。使われ方：KST Lemma 4.10 の E₁ の係数微分。 -/
theorem tensorSingleHomology_boundary
    {M N : ModuleCat.{u} R} [Module.Flat R M] [Module.Flat R N]
    (f : M ⟶ N) (K : CochainComplex (ModuleCat.{u} R) ℤ) (a q : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (tensorSingleDegreeBoundary f K a) q (q + 1) (by omega) ≫
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (singleTensorShiftIso N K (a + 1)).hom (q + 1) (q - a) (by omega) ≫
        (flatLeftTensorHomologyIso N (q - a)).hom.app K =
      (singleTensorHomologyIso M K a q).hom ≫ (f ▷ K.homology (q - a)) := by
  rw [← Category.assoc, tensorSingleHomology_shift_boundary, Category.assoc,
    flatLeftTensorHomologyIso_map]
  rfl

/-- 概要：一項テンソルのホモロジー同型を、指定した係数次数で表す。
方針：標準正規化のホモロジー、次数を明示したシフト比較、平坦係数比較を合成する。
規約：s=q-a を証明として受け取り、添字の型変換を同型に含める。
使われ方：KST Lemma 4.10 の隣接二行で係数次数を共通にする。 -/
def singleTensorHomologyIsoAt (M : ModuleCat.{u} R) [Module.Flat R M]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a q s : ℤ) (hs : q - a = s) :
    (cochainTensor ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M) K).homology q ≅
      (tensorLeft M).obj (K.homology s) :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso (singleTensorShiftIso M K a) ≪≫
    ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftIso (-a) q s (by omega)).app
      (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K) ≪≫
    (flatLeftTensorHomologyIso M s).app K

/-- 概要：指定次数の一項ホモロジー同型の正射は標準正規化のシフト誘導射と平坦比較の合成。
方針：同型の合成の定義を展開して結合順序を揃える。
規約：同型の正射をシフト列の API で表す。使われ方：KST Lemma 4.10 の境界比較。 -/
theorem singleTensorHomologyIsoAt_hom
    (M : ModuleCat.{u} R) [Module.Flat R M]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a q s : ℤ) (hs : q - a = s) :
    (singleTensorHomologyIsoAt M K a q s hs).hom =
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (singleTensorShiftIso M K a).hom q s (by omega) ≫
      (flatLeftTensorHomologyIso M s).hom.app K := by
  simp only [singleTensorHomologyIsoAt, Iso.trans_hom, Functor.mapIso_hom,
    Functor.shiftMap, Iso.app_hom, Category.assoc]
  rfl

/-- 概要：隣接する一項テンソル境界は、共通の係数次数で f ⊗ H(K) を誘導する。
方針：源と標的の次数等式で添字を正規化し、既証の境界比較を適用する。
規約：境界のホモロジー次数は一つ増え、係数次数 s は変わらない。
使われ方：KST Lemma 4.10 の初頁微分の係数次数を固定する。 -/
theorem tensorSingleHomology_boundary_at
    {M N : ModuleCat.{u} R} [Module.Flat R M] [Module.Flat R N]
    (f : M ⟶ N) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a q q' s : ℤ) (hq : q + 1 = q') (hs : q - a = s) :
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (tensorSingleDegreeBoundary f K a) q q' (by omega) ≫
      (singleTensorHomologyIsoAt N K (a + 1) q' s (by omega)).hom =
      (singleTensorHomologyIsoAt M K a q s hs).hom ≫ (f ▷ K.homology s) := by
  obtain rfl := hq
  obtain rfl := hs
  rw [singleTensorHomologyIsoAt_hom, singleTensorHomologyIsoAt_hom]
  have h := tensorSingleHomology_boundary f K a q
  change _ = ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
    (singleTensorShiftIso M K a).hom q (q - a) (by omega) ≫
    (flatLeftTensorHomologyIso M (q - a)).hom.app K) ≫ _ at h
  simpa only [Category.assoc] using h


end SerrePositivity.KST.ProExcision
