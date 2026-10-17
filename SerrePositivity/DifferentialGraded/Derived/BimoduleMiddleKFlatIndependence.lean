module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleResolutionLiftTensor
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIndependence

/-! # 任意の右相対K-flat解像度による中間比較と既存標準比較の一致

## 概要
任意の右相対K-flat解像度による中間比較と既存標準比較の一致。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

/-- semifree性を仮定せず、任意の右K-flat解像度による比較は標準比較に一致する。 -/
lemma derivedMiddleRestrictionComparison_kFlat_eq_canonical (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q := by
  let S := rightKFlatResolutionObj A D E hE
    ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  let s := (bimoduleCanonicalSemifreeResolution A D E
    ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)).π
  let r : S ⟶ R := ⟨bimoduleCanonicalResolutionLift A D E q hq⟩
  apply derivedMiddleRestrictionComparison_eq_of_squares A B C D E F hE Q S R s q
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso hq r
    (bimoduleCanonicalResolutionLift_fac A D E q hq).symm P
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P
  have h := composeAfter_bimoduleCanonicalResolutionLift_fac A B D E P₀ q hq
  change (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 P₀) r.hom) ≫
    (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 P₀) q) =
    (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 P₀) s) at h
  dsimp only [middleRestrictionResolvedMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    ← Category.assoc]
  exact congrArg (fun k => k ≫ (bimoduleToDerived A B E).map
    (middleRestrictionComparisonMap A B C D E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q.obj))) h

end SerrePositivity.DifferentialGraded.BimoduleTensor
