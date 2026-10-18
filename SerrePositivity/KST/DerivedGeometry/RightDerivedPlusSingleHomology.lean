module

public import SerrePositivity.KST.DerivedGeometry.RightDerivedPlusSingle
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
概要：bounded below 右導来関手の単一対象の正次数コホモロジーを通常の右導来関手と比較する。
方針：同じ injective 分解の零拡張の短複体を比較し、分解による二つの計算を同定する。
規約：係数層の高次切断消滅を導来圏の像のコホモロジーへ移す。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来単位の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] {X : C} (I : InjectiveResolution X)

/--
概要：分解の零拡張の微分と元の分解の微分の比較は加法的関手への適用と両立する。
方針：既存の各項の同型と微分の比較を関手で写す。
規約：二つの添字は自然数の像とする。
使われ方：TT §3、Toën §3.2 の正次数の短複体の比較。
-/
lemma appliedInjectiveResolution_d_comparison (i j : ℕ) :
    (F.mapIso (I.cochainComplexXIso i i rfl)).hom ≫ F.map (I.cocomplex.d i j) =
      F.map (I.cochainComplex.d i j) ≫ (F.mapIso (I.cochainComplexXIso j j rfl)).hom := by
  change F.map (I.cochainComplexXIso i i rfl).hom ≫ F.map (I.cocomplex.d i j) =
    F.map (I.cochainComplex.d i j) ≫ F.map (I.cochainComplexXIso j j rfl).hom
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  rw [I.cochainComplex_d i j i j rfl rfl]
  simp

/--
概要：加法的関手で写した分解の零拡張の正次数の短複体は元の分解の短複体と同型。
方針：三つの各項の既存の同型と微分の比較を使う。
規約：中央の次数は n+1>0。
使われ方：TT §3・§8、Toën §3.2 の通常の右導来関手との比較。
-/
def appliedInjectiveResolutionShortComplexIso (n : ℕ) :
    (((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).sc'
      (n : ℤ) (n + 1) (n + 2)) ≅
      (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc' n (n + 1) (n + 2)) :=
  ShortComplex.isoMk
    (F.mapIso (I.cochainComplexXIso n n rfl))
    (F.mapIso (I.cochainComplexXIso (n + 1) (n + 1) (by simp)))
    (F.mapIso (I.cochainComplexXIso (n + 2) (n + 2) (by simp)))
    (appliedInjectiveResolution_d_comparison F I n (n + 1))
    (appliedInjectiveResolution_d_comparison F I (n + 1) (n + 2))

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/--
概要：通常の正次数右導来が零なら bounded below 右導来の単一対象の同じコホモロジーも零。
方針：同じ injective 分解で二つを計算し、正次数の短複体の同型で零を移す。
規約：通常の右導来の消滅だけを入力とし、導来圏の比較を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン消滅。
-/
lemma rightDerivedPlusSingle_homology_isZero (I : InjectiveResolution X) (n : ℕ)
    (h : IsZero ((F.rightDerived (n + 1)).obj X)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D (n + 1)).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))) := by
  have hN : (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1)) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact h.of_iso (I.isoRightDerivedObj F (n + 1)).symm
  have hNs := (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).mp hN
  have hZs := (ShortComplex.exact_iff_of_iso (appliedInjectiveResolutionShortComplexIso F I n)).mpr hNs
  have hZ : ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).ExactAt (n + 1 : ℤ) :=
    (HomologicalComplex.exactAt_iff' _ (n : ℤ) (n + 1) (n + 2) (by simp) (by simp [add_assoc])).mpr hZs
  have hQ : IsZero ((DerivedCategory.Plus.homologyFunctor D (n + 1)).obj
      (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (injectiveResolutionPlus I)))) :=
    hZ.isZero_homology.of_iso ((DerivedCategory.homologyFunctorFactors D (n + 1)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex))
  exact hQ.of_iso ((DerivedCategory.Plus.homologyFunctor D (n + 1)).mapIso
    (rightDerivedPlusSingleIso F I))

end SerrePositivity.KST.DerivedGeometry
