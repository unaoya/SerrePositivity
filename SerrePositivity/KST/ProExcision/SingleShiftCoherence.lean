module

public import SerrePositivity.KST.ProExcision.SingleTensorNaturality

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 一項テンソルの隣接次数とシフトの整合性

概要：一項テンソルの正規化は、隣接二次数の境界のシフトと整合する。
方針：SingleFunctors のシフト加法則を全テンソル関手へ後合成して使う。
規約：標準のシフト加法同型を明示する。
使われ方：KST Lemma 4.10 の初頁微分のホモロジー比較。
-/

universe u v w

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

/-- 概要：一項関手族の零次数への正規化は隣接次数の境界と整合。
方針：シフト加法則の逆射の公式に、零次数からの比較射の自然性を合成する。
規約：比較射 e は任意。使われ方：KST Lemma 4.10 の一項テンソルの境界正規化。 -/
theorem singleFamilyShift_boundary
    {C : Type v} [Category C] {D : Type w} [Category D] [HasShift D ℤ]
    (F : SingleFunctors C D ℤ) (X : C) (a : ℤ) {Y : D}
    (e : (F.functor 0).obj X ⟶ Y) :
    (F.shiftIso 1 a (a + 1) (by omega)).inv.app X ≫
      ((F.shiftIso (-(a + 1)) (a + 1) 0 (by omega)).inv.app X ≫ e⟦-(a + 1)⟧')⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' D (-(a + 1)) 1 (-a) (by omega)).inv.app Y =
      (F.shiftIso (-a) a 0 (by omega)).inv.app X ≫ e⟦-a⟧' := by
  let A := shiftFunctorAdd' D (-(a + 1)) 1 (-a) (by omega)
  have hA : (e⟦-(a + 1)⟧')⟦(1 : ℤ)⟧' ≫ A.inv.app Y =
      A.inv.app ((F.functor 0).obj X) ≫ e⟦-a⟧' := A.inv.naturality e
  have hF := F.shiftIso_add'_inv_app 1 (-(a + 1)) (-a) (by omega)
    a (a + 1) 0 (by omega) (by omega) X
  rw [Functor.map_comp]
  calc
    _ = (F.shiftIso 1 a (a + 1) (by omega)).inv.app X ≫
        ((F.shiftIso (-(a + 1)) (a + 1) 0 (by omega)).inv.app X)⟦(1 : ℤ)⟧' ≫
        ((e⟦-(a + 1)⟧')⟦(1 : ℤ)⟧' ≫ A.inv.app Y) := by
          simp only [Category.assoc]
          rfl
    _ = (F.shiftIso 1 a (a + 1) (by omega)).inv.app X ≫
        ((F.shiftIso (-(a + 1)) (a + 1) 0 (by omega)).inv.app X)⟦(1 : ℤ)⟧' ≫
        (A.inv.app ((F.functor 0).obj X) ≫ e⟦-a⟧') := by rw [hA]
    _ = ((F.shiftIso 1 a (a + 1) (by omega)).inv.app X ≫
        ((F.shiftIso (-(a + 1)) (a + 1) 0 (by omega)).inv.app X)⟦(1 : ℤ)⟧' ≫
        A.inv.app ((F.functor 0).obj X)) ≫ e⟦-a⟧' := by simp only [Category.assoc]
    _ = _ := congrArg (fun f ↦ f ≫ e⟦-a⟧') hF.symm

variable {R : Type u} [CommRing R]

/-- 概要：一項複体の族を全テンソル関手へ後合成した一項関手族。
方針：右テンソル関手のシフト可換構造を使う。
規約：族のシフト同型も標準構造から得る。使われ方：KST Lemma 4.10 の境界整合性。 -/
def tensorSingleFamily (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    SingleFunctors (ModuleCat.{u} R) (CochainComplex (ModuleCat.{u} R) ℤ) ℤ :=
  (CochainComplex.singleFunctors (ModuleCat.{u} R)).postcomp (cochainTensorFixedRight K)

/-- 概要：恒等係数射による一項テンソル境界は後合成関手族の隣接シフト同型の逆。
方針：定義を展開し恒等係数射を簡約する。
規約：境界のシフトは 1。使われ方：KST Lemma 4.10 の境界のシフト整合性。 -/
theorem tensorSingleDegreeBoundary_id_family
    (M : ModuleCat.{u} R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    tensorSingleDegreeBoundary (𝟙 M) K a =
      ((tensorSingleFamily K).shiftIso 1 a (a + 1) (by omega)).inv.app M := by
  unfold tensorSingleDegreeBoundary singleDegreeBoundary
  erw [(CochainComplex.singleFunctor (ModuleCat.{u} R) a).map_id M, Category.id_comp]
  simp only [tensorSingleFamily, SingleFunctors.postcomp_shiftIso_inv_app]
  rfl

/-- 概要：一項テンソルの標準正規化は後合成関手族の零次数への逆シフトと零次数比較の合成。
方針：後合成のシフト同型の定義と同型の合成を展開する。
規約：既存 singleTensorShiftIso と同じ射。使われ方：KST Lemma 4.10 の標準比較の整合性。 -/
theorem singleTensorShiftIso_family
    (M : ModuleCat.{u} R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (singleTensorShiftIso M K a).hom =
      ((tensorSingleFamily K).shiftIso (-a) a 0 (by omega)).inv.app M ≫
        (cochainTensorSingleLeftIso M K).hom⟦-a⟧' := by
  simp only [singleTensorShiftIso, tensorSingleFamily, Iso.trans_hom,
    SingleFunctors.postcomp_shiftIso_inv_app, Category.assoc]
  rfl

/-- 概要：恒等係数の隣接境界を標準正規化で移すと恒等のシフト比較になる。
方針：後合成一項関手族のシフト加法則を、次数零テンソルの比較射に適用する。
規約：二回のシフトを標準加法同型で一回へまとめる。
使われ方：KST Lemma 4.10 の隣接係数次数の正規化。 -/
theorem tensorSingleShift_boundary_id
    (M : ModuleCat.{u} R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    tensorSingleDegreeBoundary (𝟙 M) K a ≫
      (singleTensorShiftIso M K (a + 1)).hom⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (CochainComplex (ModuleCat.{u} R) ℤ)
        (-(a + 1)) 1 (-a) (by omega)).inv.app
          (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K) =
      (singleTensorShiftIso M K a).hom := by
  rw [tensorSingleDegreeBoundary_id_family, singleTensorShiftIso_family M K (a + 1),
    singleTensorShiftIso_family M K a]
  exact singleFamilyShift_boundary (tensorSingleFamily K) M a (cochainTensorSingleLeftIso M K).hom

/-- 概要：一般の係数境界は、同次数の係数射と恒等係数境界の合成。
方針：一項境界の定義を展開し、テンソル関手の合成保存を使う。
規約：係数射は任意。使われ方：KST Lemma 4.10 の係数自然性と境界整合性の合成。 -/
theorem tensorSingleDegreeBoundary_factor
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    tensorSingleDegreeBoundary f K a =
      (cochainTensorFixedRight K).map
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).map f) ≫
      tensorSingleDegreeBoundary (𝟙 N) K a := by
  unfold tensorSingleDegreeBoundary singleDegreeBoundary
  erw [(CochainComplex.singleFunctor (ModuleCat.{u} R) a).map_id N, Category.id_comp]
  rw [(cochainTensorFixedRight K).map_comp, Category.assoc]

/-- 概要：隣接一項テンソル境界を正規化すると、通常の係数テンソル射のシフトになる。
方針：一般係数境界を恒等係数境界へ分解し、境界整合性と係数自然性を合成する。
規約：平坦性を使わず複体射として比較する。
使われ方：KST Lemma 4.10 の初頁微分を係数ホモロジーへ比較する直前の等式。 -/
theorem tensorSingleShift_boundary
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    tensorSingleDegreeBoundary f K a ≫
      (singleTensorShiftIso N K (a + 1)).hom⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (CochainComplex (ModuleCat.{u} R) ℤ)
        (-(a + 1)) 1 (-a) (by omega)).inv.app
          (((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj K) =
      (singleTensorShiftIso M K a).hom ≫
        ((((curriedTensor (ModuleCat.{u} R)).map f).mapHomologicalComplex (.up ℤ)).app K)⟦-a⟧' := by
  rw [tensorSingleDegreeBoundary_factor, Category.assoc, tensorSingleShift_boundary_id]
  exact singleTensorShiftIso_coefficient f K a

end SerrePositivity.KST.ProExcision
