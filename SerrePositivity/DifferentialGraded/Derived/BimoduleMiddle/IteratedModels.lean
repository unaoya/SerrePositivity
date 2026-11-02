module

public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Endomorphism.Perfect
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.DifferentialGraded.Derived.Functor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.DifferentialGraded.Derived.Bimodule
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence

/-!
# Derived.BimoduleMiddle.IteratedModels

## 概要
導来制限の shift・三角性と二段階制限のモデル計算をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## RestrictionShift（旧 SerrePositivity/DifferentialGraded/Derived/RestrictionShift.lean） -/

/-! # 導来制限の全Homモデルと整合的整数shift

## 概要
導来制限の全Homモデルと整合的整数shift。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionShift
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedRestriction_enriched_fac :
    moduleToDerived A E ⋙ dgDerivedRestriction A D E F =
      (dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D := by
  rw [dgModuleRestriction_onClosed_eq]
  exact dgDerivedRestriction_fac A D E F

instance dgDerivedRestriction_enriched_lifting :
    Localization.Lifting (moduleToDerived A E) (moduleQuasiIso A E)
      ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
      (dgDerivedRestriction A D E F) := ⟨eqToIso (dgDerivedRestriction_enriched_fac A D E F)⟩

/-- U14の全dg関手用shift比較を局所化し、既存の導来制限に与える。 -/
@[instance_reducible]
def dgDerivedRestrictionCommShift : (dgDerivedRestriction A D E F).CommShift ℤ := by
  letI := dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
  exact Functor.commShiftOfLocalization (moduleToDerived A E) (moduleQuasiIso A E) ℤ
    ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
    (dgDerivedRestriction A D E F)

section
local instance : (dgModuleRestriction A D E F.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F

lemma dgDerivedRestrictionFac_commShift :
    NatTrans.CommShift (eqToIso (dgDerivedRestriction_enriched_fac A D E F)).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleToDerived A E) (moduleQuasiIso A E)
      ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
      (dgDerivedRestriction A D E F)).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization (moduleToDerived A E) (moduleQuasiIso A E) ℤ
    ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
    (dgDerivedRestriction A D E F)
end
end SerrePositivity.DifferentialGraded
end

end RestrictionShift

/-! ## RestrictionTriangles（旧 SerrePositivity/DifferentialGraded/Derived/RestrictionTriangles.lean） -/

/-! # 主K経由の制限と導来制限のshift整合的比較・三角性

## 概要
主K経由の制限と導来制限のshift整合的比較・三角性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionTriangles
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- dg制限を主Kで適用する経路と、主導来制限の自然な正方形。 -/
def dgDerivedRestrictionHomotopyIso :
    (dgModuleRestriction A D E F.op).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D ≅
      moduleHomotopyToDerivedClosed A E ⋙ dgDerivedRestriction A D E F :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A E))
    ((Functor.associator (moduleToHomotopy A E) (dgModuleRestriction A D E F.op).onHomotopy
        (moduleHomotopyToDerivedClosed A D)).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (dgModuleRestriction A D E F.op).onHomotopy_fac)
        (moduleHomotopyToDerivedClosed A D) ≪≫
      Functor.associator (dgModuleRestriction A D E F.op).onClosed
        (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D) ≪≫
      Functor.isoWhiskerLeft (dgModuleRestriction A D E F.op).onClosed
        (moduleToHomotopyDerivedIso A D) ≪≫
      (eqToIso (dgDerivedRestriction_enriched_fac A D E F)).symm ≪≫
      Functor.isoWhiskerRight (moduleToHomotopyDerivedIso A E).symm
        (dgDerivedRestriction A D E F) ≪≫
      Functor.associator (moduleToHomotopy A E) (moduleHomotopyToDerivedClosed A E)
        (dgDerivedRestriction A D E F))

local instance : (dgModuleRestriction A D E F.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
local instance : (dgModuleRestriction A D E F.op).onHomotopy.CommShift ℤ :=
  dgModuleFunctorHomotopyCommShift A E D (dgModuleRestriction A D E F.op)
local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F

lemma dgModuleRestrictionHomotopyFac_commShift :
    NatTrans.CommShift (eqToIso (dgModuleRestriction A D E F.op).onHomotopy_fac).hom ℤ := by
  have he : eqToIso (dgModuleRestriction A D E F.op).onHomotopy_fac =
      dgModuleFunctorHomotopyFacIso A E D (dgModuleRestriction A D E F.op) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    rfl
  rw [he]
  exact dgModuleFunctorHomotopyFacIso_commShift A E D (dgModuleRestriction A D E F.op)

lemma dgDerivedRestrictionHomotopyIso_commShift :
    NatTrans.CommShift (dgDerivedRestrictionHomotopyIso A D E F).hom ℤ := by
  let := dgModuleRestrictionHomotopyFac_commShift A D E F
  let := dgDerivedRestrictionFac_commShift A D E F
  unfold dgDerivedRestrictionHomotopyIso
  apply quotientNatIsoLift_commShift
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

lemma dgDerivedRestrictionIsTriangulated : (dgDerivedRestriction A D E F).IsTriangulated := by
  let := dgModuleFunctorHomotopyIsTriangulated A E D (dgModuleRestriction A D E F.op)
  let := dgDerivedRestrictionHomotopyIso_commShift A D E F
  exact Functor.isTriangulated_of_precomp_iso (dgDerivedRestrictionHomotopyIso A D E F).symm

lemma dgDerivedRestriction_additive : (dgDerivedRestriction A D E F).Additive := by
  rw [Localization.functor_additive_iff (moduleHomotopyToDerivedClosed A E)
    (moduleHomotopyQuasiIso A E)]
  exact Functor.additive_of_iso (dgDerivedRestrictionHomotopyIso A D E F)

end SerrePositivity.DifferentialGraded
end

end RestrictionTriangles

/-! ## CompactAdjunctionCoproducts（旧 SerrePositivity/DifferentialGraded/Derived/CompactAdjunctionCoproducts.lean） -/

/-! # dg加群導来圏のcompact保存左随伴に対する右随伴の余積保存

## 概要
dg加群導来圏のcompact保存左随伴に対する右随伴の余積保存。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompactAdjunctionCoproducts
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  (R : DerivedModuleCategory A E ⥤ DerivedModuleCategory A D) [L.Additive] [R.Additive]
  (adj : L ⊣ R)
variable {J : Type u} (G : J → DerivedModuleCategory A E)

lemma derivedAdjunction_sigmaComparison_projection (i : J) :
    sigmaComparison R G ≫ R.map (moduleDerivedCoproductProjection A E G i) =
      moduleDerivedCoproductProjection A D (fun j => R.obj (G j)) i := by
  apply Sigma.hom_ext
  intro j
  rw [ι_comp_sigmaComparison_assoc, ← CategoryTheory.Functor.map_comp]
  by_cases hji : j = i
  · subst j
    rw [moduleDerivedCoproductProjection_self, CategoryTheory.Functor.map_id,
      moduleDerivedCoproductProjection_self]
  · rw [moduleDerivedCoproductProjection_ne A E G j i hji, Functor.map_zero,
      moduleDerivedCoproductProjection_ne A D _ j i hji]

lemma derivedAdjunction_sigmaHom_injective (P : DerivedModuleCategory A D)
    (hP : moduleCompact A D P) :
    Function.Injective (fun f : P ⟶ ∐ fun j => R.obj (G j) => f ≫ sigmaComparison R G) := by
  intro f g hfg
  change f ≫ sigmaComparison R G = g ≫ sigmaComparison R G at hfg
  apply sub_eq_zero.mp
  apply moduleCompact_hom_ext_zero A D hP _ (f - g)
  intro i
  rw [← derivedAdjunction_sigmaComparison_projection A D E R G i,
    sub_comp, ← Category.assoc, ← Category.assoc, hfg, sub_self]

include adj

omit [R.Additive] in
lemma derivedAdjunction_sigmaHom_surjective (P : DerivedModuleCategory A D)
    (hLP : moduleCompact A E (L.obj P)) :
    Function.Surjective (fun f : P ⟶ ∐ fun j => R.obj (G j) => f ≫ sigmaComparison R G) := by
  classical
  intro f
  obtain ⟨t, g, hg⟩ := hLP J G ((adj.homEquiv P (∐ G)).symm f)
  refine ⟨∑ j ∈ t, adj.homEquiv P (G j) (g j) ≫
    Sigma.ι (fun j => R.obj (G j)) j, ?_⟩
  dsimp only
  rw [sum_comp]
  have he := congrArg (adj.homAddEquiv P (∐ G)) hg
  have hx : (adj.homAddEquiv P (∐ G)) ((adj.homEquiv P (∐ G)).symm f) = f :=
    (adj.homEquiv P (∐ G)).apply_symm_apply f
  rw [hx] at he
  simp only [map_sum] at he
  calc
    _ = ∑ j ∈ t, adj.homEquiv P (∐ G) (g j ≫ Sigma.ι G j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Category.assoc, ι_comp_sigmaComparison]
      exact (adj.homEquiv_naturality_right (g j) (Sigma.ι G j)).symm
    _ = f := he

lemma derivedAdjunction_sigmaComparison_isIso
    (hcompact : ∀ P : DerivedModuleCategory A D, moduleCompact A D P →
      moduleCompact A E (L.obj P)) : IsIso (sigmaComparison R G) := by
  apply moduleDerived_isIso_of_compact_hom_bijective A D
  intro P hP
  exact ⟨derivedAdjunction_sigmaHom_injective A D E R G P hP,
    derivedAdjunction_sigmaHom_surjective A D E L R adj G P (hcompact P hP)⟩

lemma derivedAdjunction_rightAdjoint_preservesCoproduct
    (hcompact : ∀ P : DerivedModuleCategory A D, moduleCompact A D P →
      moduleCompact A E (L.obj P)) : PreservesColimit (Discrete.functor G) R := by
  let := derivedAdjunction_sigmaComparison_isIso A D E L R adj G hcompact
  exact PreservesCoproduct.of_iso_comparison _ G

end SerrePositivity.DifferentialGraded
end

end CompactAdjunctionCoproducts

/-! ## BimoduleMiddleComparisonComputation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleComparisonComputation.lean） -/

/-! # 全導来中間比較を指定K-flatモデルで計算する入口

## 概要
全導来中間比較を指定K-flatモデルで計算する入口。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleComparisonComputation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor

private lemma replacementConjugate_precomp
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (E : C ⥤ D) (hE : E.FullyFaithful) (R : D ⥤ C) (ε : R ⋙ E ≅ 𝟭 D)
    (U H : D ⥤ T) (τ : E ⋙ U ⟶ E ⋙ H) (X : C) :
    U.map (ε.app (E.obj X)).inv ≫ τ.app (R.obj (E.obj X)) ≫
        H.map (ε.app (E.obj X)).hom = τ.app X := by
  let f : R.obj (E.obj X) ⟶ X := hE.preimage (ε.app (E.obj X)).hom
  have hf : E.map f = (ε.app (E.obj X)).hom := hE.map_preimage _
  have hn := τ.naturality f
  change U.map (E.map f) ≫ τ.app X = τ.app (R.obj (E.obj X)) ≫ H.map (E.map f) at hn
  rw [hf] at hn
  rw [← hn, ← Category.assoc, ← U.map_comp, Iso.inv_hom_id, U.map_id, Category.id_comp]

variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

/-- 右K-flat局所化上で、sourceを既存の導来制限表示へ移した実際の比較。 -/
def middleLocalizedRestrictionComparison :
    rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE ⟶
      rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE :=
  (middleRightKFlatSourceIdentification A B C D E F hE).inv ≫
    middleRightKFlatLocalizedComparison A B C D E F hE

/-- 全導来比較は、指定置換の余単位で局所化上の比較を移したものである。 -/
lemma derivedMiddleRestrictionNatTrans_conjugate (Q : DerivedBimoduleCategory A C E) :
    (derivedMiddleRestrictionNatTrans A B C D E F hE).app Q =
      (middleRestrictionDerivedSource A B C D E F hE).map
          ((rightKFlatReplacementCounitIso A C E hE).app Q).inv ≫
        (middleLocalizedRestrictionComparison A B C D E F hE).app
          ((derivedRightKFlatReplacement A C E hE).obj Q) ≫
        (derivedBimoduleComposeFunctor A B C E hE).map
          ((rightKFlatReplacementCounitIso A C E hE).app Q).hom := by
  dsimp only [derivedMiddleRestrictionNatTrans, middleFullDerivedSourceIdentification,
    middleFullDerivedComparison, middleFullDerivedTargetIso, middleLocalizedRestrictionComparison,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Iso.app_hom, Iso.app_inv]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  exact congrArg (fun f => (middleRestrictionDerivedSource A B C D E F hE).map
    ((rightKFlatReplacementCounitIso A C E hE).app Q).inv ≫
    (middleRightKFlatSourceIdentification A B C D E F hE).inv.app
      ((derivedRightKFlatReplacement A C E hE).obj Q) ≫
    (middleRightKFlatLocalizedComparison A B C D E F hE).app
      ((derivedRightKFlatReplacement A C E hE).obj Q) ≫ f)
    (Category.comp_id ((derivedBimoduleComposeFunctor A B C E hE).map
      ((rightKFlatReplacementCounitIso A C E hE).app Q).hom))

/-- 右K-flat局所化への制限は、元の局所化上の比較を厳密に回復する。 -/
lemma derivedMiddleRestrictionNatTrans_precomp_rightKFlat :
    whiskerLeft (rightKFlatDerivedInclusion A C E)
        (derivedMiddleRestrictionNatTrans A B C D E F hE) =
      middleLocalizedRestrictionComparison A B C D E F hE := by
  apply NatTrans.ext
  funext Q
  rw [whiskerLeft_app, derivedMiddleRestrictionNatTrans_conjugate]
  exact replacementConjugate_precomp (rightKFlatDerivedInclusion A C E)
    (rightKFlatDerivedInclusion_fullyFaithful A C E hE) (derivedRightKFlatReplacement A C E hE)
    (rightKFlatReplacementCounitIso A C E hE)
    (middleRestrictionDerivedSource A B C D E F hE)
    (derivedBimoduleComposeFunctor A B C E hE)
    (middleLocalizedRestrictionComparison A B C D E F hE) Q

lemma middleLocalizedRestrictionComparison_eq_lift :
    middleLocalizedRestrictionComparison A B C D E F hE =
      Localization.liftNatTrans (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
        (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
          middleRestrictionDerivedSource A B C D E F hE)
        (middleDerivedTargetKFlatFunctor A B C E hE)
        (rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE)
        (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE)
        ((middleSourceKFlatIdentification A B C D E F hE).inv ≫
          middleDerivedKFlatComparison A B C D E F hE) := by
  unfold middleLocalizedRestrictionComparison middleRightKFlatSourceIdentification
    middleRightKFlatLocalizedComparison
  simp only [Localization.liftNatIso_inv, Localization.comp_liftNatTrans]

lemma middleLocalizedRestrictionComparison_app (Q : RightKFlatBimoduleCategory A C E) :
    (middleLocalizedRestrictionComparison A B C D E F hE).app
        ((rightKFlatToDerived A C E).obj Q) =
      (middleDerivedSourceLiftIdentification A B C D E F hE Q).inv ≫
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q := by
  rw [middleLocalizedRestrictionComparison_eq_lift, Localization.liftNatTrans_app]
  change 𝟙 _ ≫ ((middleDerivedSourceLiftIdentification A B C D E F hE Q).inv ≫
    derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- 全導来比較を、指定された任意の右K-flat後因子上で計算する。 -/
lemma derivedMiddleRestrictionNatTrans_app_rightKFlat (Q : RightKFlatBimoduleCategory A C E) :
    (derivedMiddleRestrictionNatTrans A B C D E F hE).app ((bimoduleToDerived A C E).obj Q.obj) =
      (middleDerivedSourceLiftIdentification A B C D E F hE Q).inv ≫
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q := by
  have h := NatTrans.congr_app (derivedMiddleRestrictionNatTrans_precomp_rightKFlat
    A B C D E F hE) ((rightKFlatToDerived A C E).obj Q)
  exact h.trans (middleLocalizedRestrictionComparison_app A B C D E F hE Q)

lemma middleRightKFlatComparison_eq_first_lift (Q : RightKFlatBimoduleCategory A C E) :
    (middleDerivedSourceLiftIdentification A B C D E F hE Q).inv ≫
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q =
      Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
        (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
          ((bimoduleToDerived A C E).obj Q.obj))
        (middleDerivedTargetFamily A B C E hE Q)
        ((middleRestrictionDerivedSource A B C D E F hE).obj
          ((bimoduleToDerived A C E).obj Q.obj))
        ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
        ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).inv ≫
          derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q) := by
  rw [← derivedMiddleRestrictionCanonicalFamily_lift]
  unfold middleDerivedSourceLiftIdentification
  simp only [Localization.liftNatIso_inv, Localization.comp_liftNatTrans]

/-- 既存の全導来制限表示における比較を、元の閉零前因子と右K-flat後因子で計算する。 -/
lemma derivedMiddleRestrictionNatTrans_app_base (Q : RightKFlatBimoduleCategory A C E)
    (P : BimoduleCategory A B C) :
    ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
        ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) =
      (middleDerivedSourceFamilyIdentification A B C D E F hE Q).inv.app P ≫
        derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q := by
  have h := NatTrans.congr_app
    (derivedMiddleRestrictionNatTrans_app_rightKFlat A B C D E F hE Q)
    ((bimoduleToDerived A B C).obj P)
  refine h.trans ?_
  have h' := NatTrans.congr_app
    (middleRightKFlatComparison_eq_first_lift A B C D E F hE Q)
    ((bimoduleToDerived A B C).obj P)
  refine h'.trans ?_
  rw [Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.iso, middleRestrictionSourceTarget_lifting,
    middleDerivedTargetFamily_lifting, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  rw [Category.id_comp]
  simp only [NatTrans.comp_app, derivedMiddleRestrictionCanonicalFamily_app]
  exact Category.comp_id
    ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).inv.app P ≫
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleComparisonComputation

/-! ## BimoduleMiddleCompositeFamily（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleCompositeFamily.lean） -/

/-! # 二段階の中間dg圏制限による全導来合成比較のsource

## 概要
二段階の中間dg圏制限による全導来合成比較のsource。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleCompositeFamily
universe u v w z t s

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 二段階の比較を合成する際の、両変数の全導来圏上の実際のsource。 -/
def middleIteratedDerivedSource : DerivedBimoduleCategory A T L ⥤
    (DerivedBimoduleCategory A B T ⥤ DerivedBimoduleCategory A B L) :=
  derivedBimoduleRestriction A E L T L G (DGFunctor.id L) ⋙
    middleRestrictionDerivedSource A B E D L F hL ⋙
      (whiskeringLeft _ _ _).obj
        (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G)

/-- 左右の導来制限の合成同型だけから構成するsourceの正規化。 -/
def middleIteratedDerivedSourceIso :
    middleIteratedDerivedSource A B D E T L F G hL ≅
      middleRestrictionDerivedSource A B T D L (F.comp G) hL :=
  Functor.isoWhiskerRight (middleRightDerivedCompIso A L D E T F G)
      (derivedBimoduleComposeFunctor A B D L hL ⋙
        (whiskeringLeft _ _ _).obj
          (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G ⋙
            derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)) ≪≫
    Functor.isoWhiskerLeft
      (derivedBimoduleRestriction A D L T L (F.comp G) (DGFunctor.id L) ⋙
        derivedBimoduleComposeFunctor A B D L hL)
      ((whiskeringLeft _ _ _).mapIso (middleLeftDerivedCompIso A B D E T F G))

/-- 既存の全導来中間比較を実際に二段階で適用した自然変換。 -/
def middleIteratedDerivedComparison :
    middleIteratedDerivedSource A B D E T L F G hL ⟶
      derivedBimoduleComposeFunctor A B T L hL :=
  whiskerRight
      (whiskerLeft (derivedBimoduleRestriction A E L T L G (DGFunctor.id L))
        (derivedMiddleRestrictionNatTrans A B E D L F hL))
      ((whiskeringLeft _ _ _).obj
        (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G)) ≫
    derivedMiddleRestrictionNatTrans A B T E L G hL

/-- sourceの正規化は右制限の合成比較、次に左制限の合成比較を適用する。 -/
lemma middleIteratedDerivedSourceIso_hom_app
    (Q : DerivedBimoduleCategory A T L) (P : DerivedBimoduleCategory A B T) :
    ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app Q).app P =
      ((derivedBimoduleComposeFunctor A B D L hL).map
        ((middleRightDerivedCompIso A L D E T F G).hom.app Q)).app
          ((derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).obj
            ((derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj P)) ≫
        ((derivedBimoduleComposeFunctor A B D L hL).obj
          ((derivedBimoduleRestriction A D L T L (F.comp G) (DGFunctor.id L)).obj Q)).map
          ((middleLeftDerivedCompIso A B D E T F G).hom.app P) := rfl

/-- 二段階比較の成分は既存の実際の比較二つの合成である。 -/
lemma middleIteratedDerivedComparison_app
    (Q : DerivedBimoduleCategory A T L) (P : DerivedBimoduleCategory A B T) :
    ((middleIteratedDerivedComparison A B D E T L F G hL).app Q).app P =
      ((derivedMiddleRestrictionNatTrans A B E D L F hL).app
        ((derivedBimoduleRestriction A E L T L G (DGFunctor.id L)).obj Q)).app
          ((derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj P) ≫
        ((derivedMiddleRestrictionNatTrans A B T E L G hL).app Q).app P := rfl

include hL in
/-- 全導来関手族の等式は、右K-flat後因子と任意の閉零前因子で検査できる。 -/
lemma middleDerivedFamily_ext
    {U V : DerivedBimoduleCategory A T L ⥤
      (DerivedBimoduleCategory A B T ⥤ DerivedBimoduleCategory A B L)}
    {α β : U ⟶ V}
    (h : ∀ (Q : RightKFlatBimoduleCategory A T L) (P : BimoduleCategory A B T),
      (α.app ((bimoduleToDerived A T L).obj Q.obj)).app
          ((bimoduleToDerived A B T).obj P) =
        (β.app ((bimoduleToDerived A T L).obj Q.obj)).app
          ((bimoduleToDerived A B T).obj P)) : α = β := by
  apply bimoduleDerivedNatTrans_ext A T L
  intro Q
  let R := rightKFlatResolutionObj A T L hL Q
  let e := rightKFlatResolutionDerivedIso A T L hL Q
  apply (cancel_epi (U.map e.hom)).mp
  rw [α.naturality, β.naturality]
  have hh : α.app ((bimoduleToDerived A T L).obj R.obj) =
      β.app ((bimoduleToDerived A T L).obj R.obj) := by
    apply bimoduleDerivedNatTrans_ext A B T
    exact h R
  exact congrArg (fun f => f ≫ V.map e.hom) hh

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleCompositeFamily

/-! ## BimoduleMiddleCompositePresentation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleCompositePresentation.lean） -/

/-! # 二段階中間比較の閉零表示と合成正規化の可換性

## 概要
二段階中間比較の閉零表示と合成正規化の可換性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleCompositePresentation
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor

private lemma bifunctor_square
    {C D E : Type*} [Category* C] [Category* D] [Category* E] (H : C ⥤ D ⥤ E)
    {r₀ r₁ r₂ r₃ : C} {l₀ l₁ l₂ l₃ : D}
    (a : r₀ ⟶ r₁) (b : r₁ ⟶ r₂) (c : r₀ ⟶ r₃) (d : r₃ ⟶ r₂)
    (x : l₀ ⟶ l₁) (y : l₁ ⟶ l₂) (z : l₀ ⟶ l₃) (w : l₃ ⟶ l₂)
    (hr : a ≫ b = c ≫ d) (hl : x ≫ y = z ≫ w) :
    (H.obj r₀).map x ≫ (H.map a).app l₁ ≫ (H.map b).app l₁ ≫ (H.obj r₂).map y =
      (H.map c).app l₀ ≫ (H.obj r₃).map z ≫ (H.obj r₃).map w ≫ (H.map d).app l₂ := by
  have hn := (H.map (a ≫ b)).naturality y
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc] at hn
  calc
    _ = (H.obj r₀).map x ≫ (H.obj r₀).map y ≫ (H.map (a ≫ b)).app l₂ := by
      simpa only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
        using congrArg (fun f => (H.obj r₀).map x ≫ f) hn.symm
    _ = (H.obj r₀).map (z ≫ w) ≫ (H.map (c ≫ d)).app l₂ := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hl, hr]
    _ = _ := by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        NatTrans.comp_app]
      simp only [Category.assoc]
      rw [(H.map c).naturality_assoc, (H.map c).naturality_assoc]

variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 閉零両因子上の二段階sourceを既存の全導来sourceへ送る表示同型。 -/
def middleIteratedClosedSourceIso (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≅
    ((middleIteratedDerivedSource A B D E T L F G hL).obj
      ((bimoduleToDerived A T L).obj Q)).obj ((bimoduleToDerived A B T).obj P) :=
  ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)))).mapIso
      ((middleLeftIteratedDerivedIso A B D E T F G).app P) ≪≫
    ((derivedBimoduleComposeFunctor A B D L hL).mapIso
      ((middleRightIteratedDerivedIso A L D E T F G).app Q)).app
      ((derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).obj
        ((derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj
          ((bimoduleToDerived A B T).obj P)))

/-- 直接左右制限の合成同型による、閉零表示上のsource正規化。 -/
def middleIteratedClosedNormalizationIso
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≅
    (middleClosedSourceFunctor A B T D L (F.comp G) hL).obj Q |>.obj P :=
  ((derivedBimoduleComposeFunctor A B D L hL).mapIso
      ((bimoduleToDerived A D L).mapIso
        ((BimoduleCategory.middleRightRestrictionCompIso A D L E T F G).app Q))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≪≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q))).mapIso
      ((bimoduleToDerived A B D).mapIso
        ((BimoduleCategory.middleLeftRestrictionCompIso A B D E T F G).app P))

/-- 全導来sourceの正規化は、直接制限の閉零表示における正規化と可換。 -/
lemma middleIteratedClosedSourceIso_normalize
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T) :
    (middleIteratedClosedSourceIso A B D E T L F G hL Q P).hom ≫
        ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app
          ((bimoduleToDerived A T L).obj Q)).app ((bimoduleToDerived A B T).obj P) =
      (middleIteratedClosedNormalizationIso A B D E T L F G hL Q P).hom ≫
        ((middleClosedSourceIdentification A B T D L (F.comp G) hL).hom.app Q).app P := by
  have hr := NatTrans.congr_app
    (middleRightIteratedDerivedIso_normalize A L D E T F G) Q
  have hl := NatTrans.congr_app
    (middleLeftIteratedDerivedIso_normalize A B D E T F G) P
  have h := bifunctor_square (derivedBimoduleComposeFunctor A B D L hL)
    ((middleRightIteratedDerivedIso A L D E T F G).hom.app Q)
    ((middleRightDerivedCompIso A L D E T F G).hom.app
      ((bimoduleToDerived A T L).obj Q))
    ((bimoduleToDerived A D L).map
      ((BimoduleCategory.middleRightRestrictionCompIso A D L E T F G).hom.app Q))
    ((middleRightRestrictionDerivedIso A T D (F.comp G) L).hom.app Q)
    ((middleLeftIteratedDerivedIso A B D E T F G).hom.app P)
    ((middleLeftDerivedCompIso A B D E T F G).hom.app ((bimoduleToDerived A B T).obj P))
    ((bimoduleToDerived A B D).map
      ((BimoduleCategory.middleLeftRestrictionCompIso A B D E T F G).hom.app P))
    ((middleLeftRestrictionDerivedIso A B T D (F.comp G)).hom.app P) hr hl
  simpa only [middleIteratedClosedSourceIso, middleIteratedClosedNormalizationIso,
    middleIteratedDerivedSourceIso, middleClosedSourceIdentification,
    Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, whiskeringLeft, Functor.comp_obj,
    Functor.comp_map, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleCompositePresentation

/-! ## BimoduleMiddleTransportComputation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleTransportComputation.lean） -/

/-! # 全導来中間比較の表示移送付きモデル計算

## 概要
全導来中間比較の表示移送付きモデル計算。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleTransportComputation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

/-- source表示同型を前合成すると、元の標準モデル計算を回復する。 -/
lemma derivedMiddleRestrictionNatTrans_base_fac
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
        ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
          ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q := by
  rw [derivedMiddleRestrictionNatTrans_app_base, ← Category.assoc,
    Iso.hom_inv_id_app, Category.id_comp]

/-- 任意の導来射で両因子を移送した全導来比較を、指定右K-flatモデルで計算する。 -/
lemma derivedMiddleRestrictionNatTrans_transport_fac
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C)
    (Q' : DerivedBimoduleCategory A C E) (P' : DerivedBimoduleCategory A B C)
    (g : (bimoduleToDerived A C E).obj Q.obj ⟶ Q')
    (f : (bimoduleToDerived A B C).obj P ⟶ P') :
    (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
        ((middleRestrictionDerivedSource A B C D E F hE).map g).app
          ((bimoduleToDerived A B C).obj P) ≫
        ((middleRestrictionDerivedSource A B C D E F hE).obj Q').map f ≫
        ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q').app P' =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q ≫
        ((derivedBimoduleComposeFunctor A B C E hE).map g).app
          ((bimoduleToDerived A B C).obj P) ≫
        ((derivedBimoduleComposeFunctor A B C E hE).obj Q').map f := by
  have hQ := NatTrans.congr_app
    ((derivedMiddleRestrictionNatTrans A B C D E F hE).naturality g)
    ((bimoduleToDerived A B C).obj P)
  have hP := ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q').naturality f
  simp only [NatTrans.comp_app] at hQ
  rw [hP, ← Category.assoc _ _
    (((derivedBimoduleComposeFunctor A B C E hE).obj Q').map f), hQ]
  simpa only [Category.assoc] using congrArg (fun k => k ≫
    ((derivedBimoduleComposeFunctor A B C E hE).map g).app
      ((bimoduleToDerived A B C).obj P) ≫
    ((derivedBimoduleComposeFunctor A B C E hE).obj Q').map f)
    (derivedMiddleRestrictionNatTrans_base_fac A B C D E F hE Q P)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleTransportComputation

/-! ## BimoduleMiddleFullCalculation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleFullCalculation.lean） -/

/-! # 全導来中間比較を任意の指定モデルと出力制限で計算する

## 概要
全導来中間比較を任意の指定モデルと出力制限で計算する。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleFullCalculation
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

/-- 中間比較のsource表示を、前因子・後因子の既存制限表示に分けた成分式。 -/
lemma middleDerivedSourceFamilyIdentification_hom_app_calc :
    (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P =
      ((derivedBimoduleComposeFunctor A B D E hE).obj
        ((bimoduleToDerived A D E).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))).map
          ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      ((derivedBimoduleComposeFunctor A B D E hE).map
        ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj)).app
          ((derivedBimoduleRestriction A B D B C (DGFunctor.id B) F).obj
            ((bimoduleToDerived A B C).obj P)) := rfl

/-- 全導来中間比較のモデル計算は、制限後の任意の右相対K-flat解像度で行える。 -/
lemma derivedMiddleRestrictionNatTrans_resolution_calculation :
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
      (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
      ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
        ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom =
    (bimoduleToDerived A B E).map
      (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) := by
  rw [← Category.assoc ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P),
    derivedMiddleRestrictionNatTrans_base_fac,
    ← derivedMiddleRestrictionComparison_kFlat_eq_canonical A B C D E F hE Q R q hq P]
  exact derivedMiddleRestrictionComparison_calculation A B C D E F hE P Q R q hq

variable (K : Type s) [DGCategory A K] [Small.{u} K] (G : DGFunctor A K B)

local notation "S" => BimoduleCategory.of A B E
  (compose A B D E (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))
    (BimoduleCategory.underlying A D E R.obj))
local notation "T" => BimoduleCategory.of A B E
  (compose A B C E (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q.obj))
local notation "RG" => derivedBimoduleRestriction A K E B E G (DGFunctor.id E)

/-- 全導来比較のモデル計算と、既存の出力側右制限表示の可換square。 -/
lemma derivedMiddleRestrictionNatTrans_resolution_output_restriction :
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫
      (RG).map
        ((middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
          (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
          ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
            ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
          (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom) =
    (bimoduleToDerived A K E).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B K E G).map
          (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) ≫
      (middleRightRestrictionDerivedIso A B K G E).hom.app T := by
  have h := derivedMiddleRestrictionNatTrans_resolution_calculation A B C D E F hE P Q R q hq
  have hh := congrArg (fun k =>
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫ (RG).map k) h
  exact hh.trans ((middleRightRestrictionDerivedIso A B K G E).hom.naturality
    (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleFullCalculation

/-! ## BimoduleRestrictionModelCalculation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRestrictionModelCalculation.lean） -/

/-! # 外側右制限と全導来中間比較を組み合わせた任意モデル計算

## 概要
外側右制限と全導来中間比較を組み合わせた任意モデル計算。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRestrictionModelCalculation
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (K : Type s) [DGCategory A K] [Small.{u} K] (G : DGFunctor A K B)
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "LP" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P
local notation "RQ" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A C D E F) Q.obj
local notation "GP" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A B K D G) LP
local notation "RG" => derivedBimoduleRestriction A K E B E G (DGFunctor.id E)
local notation "T" => BimoduleCategory.of A B E
  (compose A B C E (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q.obj))

/-- 指定モデルから、入力の右制限表示と全導来外側右比較を続けた射。 -/
def restrictedMiddleModelPrefix :=
    (derivedBimoduleComposeResolutionComputation A K D E hE RQ R q hq).inv.app
        ((bimoduleToDerived A K D).obj GP) ≫
      ((derivedBimoduleComposeFunctor A K D E hE).obj ((bimoduleToDerived A D E).obj RQ)).map
        ((middleRightRestrictionDerivedIso A B K G D).hom.app LP) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B K D E G hE).hom.app
        ((bimoduleToDerived A D E).obj RQ)).app ((bimoduleToDerived A B D).obj LP)

private lemma paste_model_square
    {X Y : Type*} [Category* X] [Category* Y] (V : X ⥤ Y)
    {a b : Y} {x y z : X} (s : x ≅ y) (f : x ⟶ z)
    (h : a ⟶ V.obj x) (g : a ⟶ b) (e : b ⟶ V.obj y) (t : b ⟶ V.obj z)
    (h₁ : h ≫ V.map s.hom = g ≫ e) (h₂ : e ≫ V.map (s.inv ≫ f) = t) :
    h ≫ V.map f = g ≫ t := by
  have hs : h = g ≫ e ≫ V.map s.inv := by
    have hh := congrArg (fun k => k ≫ V.map s.inv) h₁
    simpa only [Category.assoc, ← V.map_comp, s.hom_inv_id, V.map_id,
      Category.comp_id] using hh
  rw [hs]
  simp only [Category.assoc]
  rw [← V.map_comp, h₂]

/-- 外側・中間の実際の全導来比較を、同じ指定解像度で通常の比較射へ計算する。 -/
lemma derivedBimoduleRestriction_model_calculation :
    restrictedMiddleModelPrefix A B C D E F K G hE P Q R q hq ≫
      (RG).map
        ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
          ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
            ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
          (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom) =
    (bimoduleToDerived A K E).map (composeRightRestrictionIso A B K D E G LP R.obj).hom ≫
      (bimoduleToDerived A K E).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B K E G).map
          (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) ≫
      (middleRightRestrictionDerivedIso A B K G E).hom.app T := by
  let s := middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq
  let b := (bimoduleToDerived A K E).map
    (composeRightRestrictionIso A B K D E G LP R.obj).hom
  let e := (middleRightRestrictionDerivedIso A B K G E).hom.app
    ((composeWith A B D E R.obj).obj LP)
  have hc := derivedBimoduleComposeRightRestrictionIso_resolution_app_calc
    A B K D E G hE RQ R q hq LP
  have hs : s.hom =
      (derivedBimoduleComposeResolutionComputation A B D E hE RQ R q hq).hom.app
        ((bimoduleToDerived A B D).obj LP) := by
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  apply paste_model_square (RG) s
    ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
      ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
        ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom)
    (restrictedMiddleModelPrefix A B C D E F K G hE P Q R q hq) b e
  · simpa only [hs, restrictedMiddleModelPrefix, Category.assoc] using hc
  · exact derivedMiddleRestrictionNatTrans_resolution_output_restriction
      (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) (hE := hE)
      (P := P) (Q := Q) (R := R) (q := q) (hq := hq) (K := K) (G := G)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleRestrictionModelCalculation

/-! ## BimoduleRestrictionSourceNormalization（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRestrictionSourceNormalization.lean） -/

/-! # 外側右制限と中間比較のsource表示の正規化

## 概要
外側右制限と中間比較のsource表示の正規化。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRestrictionSourceNormalization
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (K : Type s) [DGCategory A K] [Small.{u} K] (G : DGFunctor A K B)
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E)

local notation "LP" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P
local notation "GP" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A B K D G) LP
local notation "RQ₀" => Functor.obj (bimoduleToDerived A D E)
  (Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A C D E F) Q.obj)
local notation "RQ₁" => Functor.obj
  (derivedBimoduleRestriction A D E C E F (DGFunctor.id E))
  (Functor.obj (bimoduleToDerived A C E) Q.obj)
local notation "HK" => derivedBimoduleComposeFunctor A K D E hE
local notation "HB" => derivedBimoduleComposeFunctor A B D E hE
local notation "RG" => derivedBimoduleRestriction A K E B E G (DGFunctor.id E)

/-- 後因子の制限表示から、外側比較を経て前因子の左制限表示へ進む実際のsource経路。 -/
def restrictedMiddleSourcePrefix :=
  ((HK).map ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj)).app
      ((bimoduleToDerived A K D).obj GP) ≫
    ((HK).obj RQ₁).map ((middleRightRestrictionDerivedIso A B K G D).hom.app LP) ≫
    ((derivedBimoduleComposeRightRestrictionIso A B K D E G hE).hom.app RQ₁).app
      ((bimoduleToDerived A B D).obj LP) ≫
    (RG).map (((HB).obj RQ₁).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P))

private lemma paste_source_squares {V : Type*} [Category* V]
    {a b c d e f g h : V} (r : a ⟶ b) (p : b ⟶ c) (β : c ⟶ d) (u : d ⟶ h)
    (p₀ : a ⟶ e) (r' : e ⟶ c) (β₀ : e ⟶ f) (v : f ⟶ d) (u₀ : f ⟶ g) (v' : g ⟶ h)
    (h₁ : r ≫ p = p₀ ≫ r') (h₂ : r' ≫ β = β₀ ≫ v) (h₃ : v ≫ u = u₀ ≫ v') :
    r ≫ p ≫ β ≫ u = p₀ ≫ β₀ ≫ u₀ ≫ v' := by
  rw [← Category.assoc r p, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc r' β, h₂]
  simp only [Category.assoc]
  rw [h₃]

/-- 後因子の制限表示を外側比較の自然性で移すと、既存の中間source表示に一致する。 -/
lemma restrictedMiddleSourcePrefix_normalize :
    restrictedMiddleSourcePrefix A B C D E F K G hE P Q =
      ((HK).obj RQ₀).map ((middleRightRestrictionDerivedIso A B K G D).hom.app LP) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B K D E G hE).hom.app RQ₀).app
        ((bimoduleToDerived A B D).obj LP) ≫
      (RG).map ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P) := by
  let r := (HK).map ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj)
  let v := (HB).map ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj)
  let p := (middleRightRestrictionDerivedIso A B K G D).hom.app LP
  let u := (middleLeftRestrictionDerivedIso A B C D F).hom.app P
  have h₁ := (r.naturality p).symm
  have h₂ := NatTrans.congr_app
    ((derivedBimoduleComposeRightRestrictionIso A B K D E G hE).hom.naturality
      ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj))
    ((bimoduleToDerived A B D).obj LP)
  simp only [NatTrans.comp_app] at h₂
  have h₃ := congrArg (RG).map (v.naturality u).symm
  simp only [CategoryTheory.Functor.map_comp] at h₃
  rw [middleDerivedSourceFamilyIdentification_hom_app_calc, CategoryTheory.Functor.map_comp]
  exact paste_source_squares _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃

/-- source正規化を任意の指定解像度の計算同型へ接続した式。 -/
lemma restrictedMiddleSourcePrefix_model
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    (derivedBimoduleComposeResolutionComputation A K D E hE
        ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj) R q hq).inv.app
        ((bimoduleToDerived A K D).obj GP) ≫
      restrictedMiddleSourcePrefix A B C D E F K G hE P Q =
    restrictedMiddleModelPrefix A B C D E F K G hE P Q R q hq ≫
      (RG).map ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P) := by
  have h := congrArg (fun k =>
    (derivedBimoduleComposeResolutionComputation A K D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj) R q hq).inv.app
      ((bimoduleToDerived A K D).obj GP) ≫ k)
    (restrictedMiddleSourcePrefix_normalize A B C D E F K G hE P Q)
  simpa only [restrictedMiddleModelPrefix, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleRestrictionSourceNormalization
