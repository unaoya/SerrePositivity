module

public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.Limits
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Restriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Module.FreeSphere

/-!
# Derived.Functor

## 概要
12 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Coproducts（旧 SerrePositivity/DifferentialGraded/Derived/Coproducts.lean） -/

/-! # 射影解像度から構成する導来加群圏の余積 -/

@[expose] public section Coproducts
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

lemma moduleProjectiveDerivedHomEquiv_precompose {P Q N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P)
    (hQ : moduleHomotopicallyProjective A D Q) (f : P ⟶ Q)
    (g : (moduleToHomotopy A D).obj Q ⟶ (moduleToHomotopy A D).obj N) :
    (moduleToDerived A D).map f ≫ moduleProjectiveDerivedHomEquiv A D hQ N g =
      moduleProjectiveDerivedHomEquiv A D hP N ((moduleToHomotopy A D).map f ≫ g) := by
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  rw [← CategoryTheory.Functor.map_comp, moduleProjectiveDerivedHomEquiv_map,
    moduleProjectiveDerivedHomEquiv_map, CategoryTheory.Functor.map_comp]

def moduleProjectiveDerivedCofan (M : J → ModuleCategory A D) :
    Cofan (fun j => (moduleToDerived A D).obj (M j)) :=
  Cofan.mk ((moduleToDerived A D).obj (∐ M))
    (fun j => (moduleToDerived A D).map (Sigma.ι M j))

def moduleProjectiveDerivedCofanDesc (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    (s : Cofan (fun j => (moduleToDerived A D).obj (M j))) :
    (moduleToDerived A D).obj (∐ M) ⟶ s.pt :=
  moduleProjectiveDerivedHomEquiv A D (moduleCoproduct_homotopicallyProjective A D M hM)
    s.pt.as.obj
    (moduleHomotopyCofanDesc A D M
      (Cofan.mk ((moduleToHomotopy A D).obj s.pt.as.obj) (fun j =>
        (moduleProjectiveDerivedHomEquiv A D (hM j) s.pt.as.obj).symm (s.inj j))))

lemma moduleProjectiveDerivedCofanDesc_fac (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    (s : Cofan (fun j => (moduleToDerived A D).obj (M j))) (j : J) :
    (moduleToDerived A D).map (Sigma.ι M j) ≫
      moduleProjectiveDerivedCofanDesc A D M hM s = s.inj j := by
  unfold moduleProjectiveDerivedCofanDesc
  rw [moduleProjectiveDerivedHomEquiv_precompose A D (hM j)
    (moduleCoproduct_homotopicallyProjective A D M hM), moduleHomotopyCofanDesc_fac]
  exact (moduleProjectiveDerivedHomEquiv A D (hM j) s.pt.as.obj).apply_symm_apply _

lemma moduleProjectiveDerivedCoproduct_hom_ext (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    {N : DerivedModuleCategory A D} {f g : (moduleToDerived A D).obj (∐ M) ⟶ N}
    (h : ∀ j, (moduleToDerived A D).map (Sigma.ι M j) ≫ f =
      (moduleToDerived A D).map (Sigma.ι M j) ≫ g) : f = g := by
  let e := moduleProjectiveDerivedHomEquiv A D
    (moduleCoproduct_homotopicallyProjective A D M hM) N.as.obj
  obtain ⟨f, rfl⟩ := e.surjective f
  obtain ⟨g, rfl⟩ := e.surjective g
  apply congrArg e
  apply moduleHomotopyCoproduct_hom_ext A D M
  intro j
  apply (moduleProjectiveDerivedHomEquiv A D (hM j) N.as.obj).injective
  exact (moduleProjectiveDerivedHomEquiv_precompose A D (hM j)
    (moduleCoproduct_homotopicallyProjective A D M hM) (Sigma.ι M j) f).symm.trans
      ((h j).trans (moduleProjectiveDerivedHomEquiv_precompose A D (hM j)
        (moduleCoproduct_homotopicallyProjective A D M hM) (Sigma.ι M j) g))

def moduleProjectiveDerivedCofanIsColimit (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j)) :
    IsColimit (moduleProjectiveDerivedCofan A D M) :=
  Cofan.IsColimit.mk _ (moduleProjectiveDerivedCofanDesc A D M hM)
    (moduleProjectiveDerivedCofanDesc_fac A D M hM) (by
      intro s m hm
      apply moduleProjectiveDerivedCoproduct_hom_ext A D M hM
      intro j
      exact (hm j).trans (moduleProjectiveDerivedCofanDesc_fac A D M hM s j).symm)

/-- 任意のu-smallな導来対象族に対する余積。 -/
instance moduleDerivedHasCoproductsOfShape :
    HasColimitsOfShape (Discrete J) (DerivedModuleCategory A D) where
  has_colimit F := by
    let R := fun j : J => moduleCanonicalProjectiveResolution A D (F.obj ⟨j⟩).as.obj
    let P := fun j : J => (R j).obj
    have : HasColimit (Discrete.functor (fun j => (moduleToDerived A D).obj (P j))) :=
      ⟨⟨moduleProjectiveDerivedCofan A D P,
        moduleProjectiveDerivedCofanIsColimit A D P (fun j => (R j).projective)⟩⟩
    let e : Discrete.functor (fun j => (moduleToDerived A D).obj (P j)) ≅ F :=
      Discrete.natIso (fun j => moduleDerivedIso A D (R j.as).π (R j.as).quasiIso)
    exact hasColimit_of_iso e.symm

end SerrePositivity.DifferentialGraded
end

end Coproducts

/-! ## RingCoproducts（旧 SerrePositivity/DifferentialGraded/Derived/RingCoproducts.lean） -/

/-! # 一対象環の導来圏比較による余積の保存 -/

@[expose] public section RingCoproducts
universe u w t

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable (J : Type t) [Small.{u} J]

instance ringDerivedEquivalencePreservesCoproducts :
    PreservesColimitsOfShape (Discrete J) (ringDerivedEquivalence A).functor := inferInstance

instance ringDerivedInversePreservesCoproducts :
    PreservesColimitsOfShape (Discrete J) (ringDerivedEquivalence A).inverse := inferInstance

/-- 指定宇宙の既存導来圏にも同じ添字の余積を移送する。 -/
instance ringDerivedTargetHasCoproducts :
    HasColimitsOfShape (Discrete J) (DerivedCategory (ModuleCat A)) :=
  Adjunction.hasColimitsOfShape_of_equivalence (ringDerivedEquivalence A).inverse

instance ringDerivedCoproductComparisonIsIso (M : J → DerivedModuleCategory A PUnit.{1}) :
    IsIso (sigmaComparison (ringDerivedEquivalence A).functor M) := inferInstance

end SerrePositivity.DifferentialGraded
end

end RingCoproducts

/-! ## IdempotentComplete（旧 SerrePositivity/DifferentialGraded/Derived/IdempotentComplete.lean） -/

/-! # 指定された非有界dg加群導来圏の冪等完備性 -/

@[expose] public section IdempotentComplete
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleDerivedIsIdempotentComplete : IsIdempotentComplete (DerivedModuleCategory A D) where
  idempotents_split X p hp := idempotent_split_of_countable_coproduct X p hp

end SerrePositivity.DifferentialGraded
end

end IdempotentComplete

/-! ## CoproductProjection（旧 SerrePositivity/DifferentialGraded/Derived/CoproductProjection.lean） -/

/-! # 導来余積の成分射と有限supportへの射影 -/

@[expose] public section CoproductProjection
universe u v

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type u} (F : J → DerivedModuleCategory A D)

def moduleDerivedCoproductProjection (j : J) : (∐ F) ⟶ F j :=
  Sigma.desc (Pi.single j (𝟙 (F j)))

lemma moduleDerivedCoproductProjection_self (j : J) :
    Sigma.ι F j ≫ moduleDerivedCoproductProjection A D F j = 𝟙 (F j) := by
  simp [moduleDerivedCoproductProjection]

lemma moduleDerivedCoproductProjection_ne (i j : J) (h : i ≠ j) :
    Sigma.ι F i ≫ moduleDerivedCoproductProjection A D F j = 0 := by
  simp [moduleDerivedCoproductProjection, h]

def moduleDerivedCoproductFiniteProjection (t : Finset J) : (∐ F) ⟶ (∐ F) :=
  ∑ j ∈ t, moduleDerivedCoproductProjection A D F j ≫ Sigma.ι F j

lemma moduleDerivedCoproductFiniteProjection_mem (t : Finset J) (i : J) (hi : i ∈ t) :
    Sigma.ι F i ≫ moduleDerivedCoproductFiniteProjection A D F t = Sigma.ι F i := by
  rw [moduleDerivedCoproductFiniteProjection, comp_sum]
  calc
    _ = Sigma.ι F i ≫ moduleDerivedCoproductProjection A D F i ≫ Sigma.ι F i :=
      Finset.sum_eq_single i
        (fun j _ hji => by
          rw [← Category.assoc, moduleDerivedCoproductProjection_ne A D F i j (Ne.symm hji)]
          exact zero_comp)
        (fun h => (h hi).elim)
    _ = _ := by
      rw [← Category.assoc, moduleDerivedCoproductProjection_self, Category.id_comp]

lemma moduleDerivedCoproductComplement_mem (t : Finset J) (i : J) (hi : i ∈ t) :
    Sigma.ι F i ≫ (𝟙 (∐ F) - moduleDerivedCoproductFiniteProjection A D F t) = 0 := by
  rw [comp_sub, Category.comp_id, moduleDerivedCoproductFiniteProjection_mem A D F t i hi,
    sub_self]

end SerrePositivity.DifferentialGraded
end

end CoproductProjection

/-! ## ModuleFunctorProjective（旧 SerrePositivity/DifferentialGraded/Derived/ModuleFunctorProjective.lean） -/

/-! # 任意dg加群関手は射影的加群間の準同型を保つ

## 概要
射影的対象間の準同型は主Kで同型であり、dg関手のH⁰関手とホモロジーがそれを保つ。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ModuleFunctorProjective
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma dgModuleFunctor_projective_quasiIso
    (L : DGFunctor A (RightModule A D) (RightModule A E))
    {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E (L.onClosed.map f) := by
  have : IsIso ((moduleToHomotopy A D).map f) :=
    moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D hM hN f hf
  apply (moduleHomotopyQuasiIso_map_iff A E (L.onClosed.map f)).1
  rw [moduleHomotopyQuasiIso_iff]
  intro e i
  change IsIso ((moduleHomotopyHomology A E e i).map
    (L.onHomotopy.map ((moduleToHomotopy A D).map f)))
  infer_instance

end SerrePositivity.DifferentialGraded
end

end ModuleFunctorProjective

/-! ## RightKFlatIsoLift（旧 SerrePositivity/DifferentialGraded/Derived/RightKFlatIsoLift.lean） -/

/-! # 右K-flatモデル上の自然同型を既存の全導来関手間へ移す

## 概要
右K-flatモデル上の自然同型を既存の全導来関手間へ移す。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightKFlatIsoLift
universe u v w z z'

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] [Small.{u} E] (hE : localHomKFlat A E)
  {T : Type z} [Category.{z'} T]

/-- 指定右K-flatモデル上の自然同型を、右K-flat部分圏の局所化上へ移す。 -/
def rightKFlatLocalizedIsoOfPrecomp (G H : DerivedBimoduleCategory A C E ⥤ T)
    (e : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ G ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ H) :
      rightKFlatDerivedInclusion A C E ⋙ G ≅ rightKFlatDerivedInclusion A C E ⋙ H := by
  letI sourceLifting : Localization.Lifting (rightKFlatToDerived A C E)
      (rightKFlatQuasiIso A C E)
      (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ G)
      (rightKFlatDerivedInclusion A C E ⋙ G) :=
    ⟨Functor.isoWhiskerRight (eqToIso (rightKFlatDerivedInclusion_fac A C E)) G⟩
  letI targetLifting : Localization.Lifting (rightKFlatToDerived A C E)
      (rightKFlatQuasiIso A C E)
      (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ H)
      (rightKFlatDerivedInclusion A C E ⋙ H) :=
    ⟨Functor.isoWhiskerRight (eqToIso (rightKFlatDerivedInclusion_fac A C E)) H⟩
  exact Localization.liftNatIso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    _ _ (rightKFlatDerivedInclusion A C E ⋙ G) (rightKFlatDerivedInclusion A C E ⋙ H) e

/-- 指定右K-flatモデル上の自然同型を、指定局所化と置換余単位で全導来圏へ移す。 -/
def rightKFlatDerivedIsoOfPrecomp (G H : DerivedBimoduleCategory A C E ⥤ T)
    (e : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ G ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ H) : G ≅ H := by
  let e' := rightKFlatLocalizedIsoOfPrecomp A C E G H e
  exact (Functor.isoWhiskerRight (rightKFlatReplacementCounitIso A C E hE) G ≪≫
      Functor.leftUnitor G).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedRightKFlatReplacement A C E hE) e' ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightKFlatReplacementCounitIso A C E hE) H ≪≫
    Functor.leftUnitor H

variable (B : Type z) [DGCategory A B] [Small.{u} B]

/-- 閉零右K-flatモデルへの前合成では、既存の全導来合成は固定因子関手族に自然同型。 -/
def rightKFlatComposePresentationIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        derivedBimoduleComposeFunctor A B C E hE ≅
      derivedComposeWithFunctor A B C E :=
  Functor.isoWhiskerRight (eqToIso (rightKFlatDerivedInclusion_fac A C E)).symm
      (derivedBimoduleComposeFunctor A B C E hE) ≪≫
    Functor.isoWhiskerLeft (rightKFlatToDerived A C E)
      (derivedBimoduleComposeKFlatFamilyIso A B C E hE) ≪≫
    eqToIso (rightFactorLocalizedComposeFunctor_fac A B C E)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightKFlatIsoLift

/-! ## RightKFlatIsoLiftComputation（旧 SerrePositivity/DifferentialGraded/Derived/RightKFlatIsoLiftComputation.lean） -/

/-! # 右K-flatモデルから移した自然同型の計算と一意性

## 概要
右K-flatモデルから移した自然同型の計算と一意性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightKFlatIsoLiftComputation
universe u v w z z'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor

private lemma fullyFaithful_conjugate
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (E : C ⥤ D) (hE : E.FullyFaithful) (R : D ⥤ C) (ε : R ⋙ E ≅ 𝟭 D)
    (G H : D ⥤ T) (τ : E ⋙ G ⟶ E ⋙ H) (X : C) :
    G.map (ε.app (E.obj X)).inv ≫ τ.app (R.obj (E.obj X)) ≫
        H.map (ε.app (E.obj X)).hom = τ.app X := by
  let f : R.obj (E.obj X) ⟶ X := hE.preimage (ε.app (E.obj X)).hom
  have hf : E.map f = (ε.app (E.obj X)).hom := hE.map_preimage _
  have hn := τ.naturality f
  change G.map (E.map f) ≫ τ.app X = τ.app (R.obj (E.obj X)) ≫ H.map (E.map f) at hn
  rw [hf] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]

variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] [Small.{u} E] (hE : localHomKFlat A E)
  {T : Type z} [Category.{z'} T]
  (G H : DerivedBimoduleCategory A C E ⥤ T)
  (e : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ G ≅
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ H)

/-- 全導来圏への移送は、指定置換余単位による局所化上の比較の共役である。 -/
lemma rightKFlatDerivedIsoOfPrecomp_conjugate (Q : DerivedBimoduleCategory A C E) :
    (rightKFlatDerivedIsoOfPrecomp A C E hE G H e).hom.app Q =
      G.map ((rightKFlatReplacementCounitIso A C E hE).app Q).inv ≫
        (rightKFlatLocalizedIsoOfPrecomp A C E G H e).hom.app
          ((derivedRightKFlatReplacement A C E hE).obj Q) ≫
        H.map ((rightKFlatReplacementCounitIso A C E hE).app Q).hom := by
  dsimp only [rightKFlatDerivedIsoOfPrecomp, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.comp_app,
    Iso.app_hom, Iso.app_inv, whiskerLeft_app, whiskerRight_app]
  simp only [Category.id_comp]
  exact congrArg (fun f => G.map ((rightKFlatReplacementCounitIso A C E hE).app Q).inv ≫
    (rightKFlatLocalizedIsoOfPrecomp A C E G H e).hom.app
      ((derivedRightKFlatReplacement A C E hE).obj Q) ≫ f)
    (Category.comp_id (H.map ((rightKFlatReplacementCounitIso A C E hE).app Q).hom))

/-- 右K-flat部分圏の局所化への前合成は元の局所化上の比較を回復する。 -/
lemma rightKFlatDerivedIsoOfPrecomp_app_inclusion
    (Q : DerivedRightKFlatBimoduleCategory A C E) :
    (rightKFlatDerivedIsoOfPrecomp A C E hE G H e).hom.app
        ((rightKFlatDerivedInclusion A C E).obj Q) =
      (rightKFlatLocalizedIsoOfPrecomp A C E G H e).hom.app Q := by
  rw [rightKFlatDerivedIsoOfPrecomp_conjugate]
  exact fullyFaithful_conjugate (rightKFlatDerivedInclusion A C E)
    (rightKFlatDerivedInclusion_fullyFaithful A C E hE) (derivedRightKFlatReplacement A C E hE)
    (rightKFlatReplacementCounitIso A C E hE) G H
    (rightKFlatLocalizedIsoOfPrecomp A C E G H e).hom Q

/-- 任意の指定右K-flatモデルで、移送前の自然同型の成分を厳密に回復する。 -/
lemma rightKFlatDerivedIsoOfPrecomp_hom_app (Q : RightKFlatBimoduleCategory A C E) :
    (rightKFlatDerivedIsoOfPrecomp A C E hE G H e).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) = e.hom.app Q := by
  have h := rightKFlatDerivedIsoOfPrecomp_app_inclusion A C E hE G H e
    ((rightKFlatToDerived A C E).obj Q)
  refine h.trans ?_
  simp only [rightKFlatLocalizedIsoOfPrecomp, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  change G.map (𝟙 _) ≫ e.hom.app Q ≫ H.map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact Category.comp_id (e.hom.app Q)

/-- 右K-flatモデルへの前合成は、指定した自然同型そのものを回復する。 -/
lemma rightKFlatDerivedIsoOfPrecomp_precomp :
    Functor.isoWhiskerLeft (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E)
        (rightKFlatDerivedIsoOfPrecomp A C E hE G H e) = e := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  exact rightKFlatDerivedIsoOfPrecomp_hom_app A C E hE G H e Q

include hE in
/-- 全導来関手の自然変換は、任意の指定右K-flatモデル上の成分で判定できる。 -/
lemma rightKFlatDerivedNatTrans_ext {U V : DerivedBimoduleCategory A C E ⥤ T} {α β : U ⟶ V}
    (h : ∀ Q : RightKFlatBimoduleCategory A C E,
      α.app ((bimoduleToDerived A C E).obj Q.obj) =
        β.app ((bimoduleToDerived A C E).obj Q.obj)) : α = β := by
  apply bimoduleDerivedNatTrans_ext A C E
  intro M
  let Q := rightKFlatResolutionObj A C E hE M
  let a := rightKFlatResolutionDerivedIso A C E hE M
  apply (cancel_epi (U.map a.hom)).mp
  rw [α.naturality, β.naturality]
  exact congrArg (fun f => f ≫ V.map a.hom) (h Q)

/-- 右K-flatモデルからの移送は恒等自然同型を保つ。 -/
lemma rightKFlatDerivedIsoOfPrecomp_refl (U : DerivedBimoduleCategory A C E ⥤ T) :
    rightKFlatDerivedIsoOfPrecomp A C E hE U U (Iso.refl _) = Iso.refl U := by
  apply Iso.ext
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  rw [rightKFlatDerivedIsoOfPrecomp_hom_app]
  rfl

/-- 右K-flatモデルからの移送は、指定自然同型の合成を保つ。 -/
lemma rightKFlatDerivedIsoOfPrecomp_trans (U V W : DerivedBimoduleCategory A C E ⥤ T)
    (e₁ : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ U ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ V)
    (e₂ : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ V ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ W) :
    rightKFlatDerivedIsoOfPrecomp A C E hE U W (e₁ ≪≫ e₂) =
      rightKFlatDerivedIsoOfPrecomp A C E hE U V e₁ ≪≫
        rightKFlatDerivedIsoOfPrecomp A C E hE V W e₂ := by
  apply Iso.ext
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  simp only [Iso.trans_hom, NatTrans.comp_app, rightKFlatDerivedIsoOfPrecomp_hom_app]

/-- 右K-flatモデルからの移送は、任意の関手への後合成とも可換。 -/
lemma rightKFlatDerivedIsoOfPrecomp_whiskerRight {S : Type*} [Category* S] (K : T ⥤ S) :
    Functor.isoWhiskerRight (rightKFlatDerivedIsoOfPrecomp A C E hE G H e) K =
      rightKFlatDerivedIsoOfPrecomp A C E hE (G ⋙ K) (H ⋙ K)
        (Functor.isoWhiskerRight e K) := by
  apply Iso.ext
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  simp only [Functor.isoWhiskerRight_hom, whiskerRight_app,
    rightKFlatDerivedIsoOfPrecomp_hom_app]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightKFlatIsoLiftComputation

/-! ## AssociatorMiddleRestrictionResolved（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionResolved.lean） -/

/-! # 第一中間圏の制限後の指定モデルと結合子の整合性

## 概要
第一中間圏の制限後の指定モデルと結合子の整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionResolved
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
  (S : BimoduleCategory A D E) (R : BimoduleCategory A E T)
  (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "S₀" => BimoduleCategory.underlying A D E S
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LP" => Bimodule.leftRestriction A B C D F P₀
local notation "LPc" => BimoduleCategory.of A B D LP
local notation "RQ" => Bimodule.rightRestriction A C D E F Q₀
local notation "QR" => BimoduleCategory.of A C T (compose A C E T Q₀ R₀)
local notation "SR" => BimoduleCategory.of A D T (compose A D E T S₀ R₀)

/-- 制限後モデルの増大を後因子と合成し、通常の右制限比較を続けた増大射。 -/
def middleRestrictionComposeAugmentation :
    SR ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D T F).obj QR :=
  composeMap A D E T q (𝟙 R) ≫ (composeRightRestrictionIso A C D E T F Q R).hom

omit [DGCategory A B] [Small.{u} B] in
/-- 後因子が右相対K-flatなら、指定増大の準同型性は合成後も保たれる。 -/
lemma middleRestrictionComposeAugmentation_quasiIso
    (hR : Bimodule.rightRelativeKFlat A E T R₀) (hq : BimoduleCategory.quasiIso A D E q) :
    BimoduleCategory.quasiIso A D T
      (middleRestrictionComposeAugmentation A C D E T F Q S R q) := by
  exact (BimoduleCategory.quasiIso A D T).comp_mem _ _
    (composeMap_first_quasiIso A D E T R hR q hq)
    ((BimoduleCategory.quasiIso A D T).of_isIso _)

private lemma prepend_square {V : Type*} [Category* V] {a b c d e f g : V}
    (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d) (t : d ⟶ e)
    (p : a ⟶ f) (α : f ⟶ c) (r : f ⟶ g) (β : g ⟶ e)
    (hn : p ≫ α = u ≫ v) (hs : α ≫ w ≫ t = r ≫ β) :
    u ≫ v ≫ w ≫ t = p ≫ r ≫ β := by
  rw [← Category.assoc u v, ← hn, Category.assoc, hs]

/-- 制限後の任意の増大を使った中間比較も、通常の結合子と可換。 -/
lemma associatorIso_middleRestriction_resolved :
    (associatorIso A B D E T LP S₀ R₀).hom ≫
      middleRestrictionResolvedMap A B C D T F P QR SR
        (middleRestrictionComposeAugmentation A C D E T F Q S R q) =
    composeMap A B E T (middleRestrictionResolvedMap A B C D E F P Q S q) (𝟙 R) ≫
      (associatorIso A B C E T P₀ Q₀ R₀).hom := by
  have hn := associatorIso_naturality A B D E T (𝟙 LPc) q (𝟙 R)
  have hs := associatorIso_middleRestriction A B C D E T F P Q R
  have hm := composeMap_comp A B D T (𝟙 LPc) (𝟙 LPc)
    (composeMap A D E T q (𝟙 R)) (composeRightRestrictionIso A C D E T F Q R).hom
  simp only [Category.id_comp] at hm
  have hc := composeMap_comp A B E T (composeMap A B D E (𝟙 LPc) q)
    (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) (𝟙 R)
  simp only [Category.id_comp] at hc
  dsimp only [middleRestrictionResolvedMap, middleRestrictionComposeAugmentation]
  rw [hm, hc]
  simp only [Category.assoc]
  have hp := prepend_square _ _ _ _ _ _ _ _ hn hs
  convert hp using 1 <;> rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionResolved

/-! ## AssociatorSecondMiddleRestrictionResolved（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorSecondMiddleRestrictionResolved.lean） -/

/-! # 第二中間圏の制限後の指定増大と通常結合子の整合性

## 概要
第二中間圏の制限後の指定増大と通常結合子の整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionResolved
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
  (R : BimoduleCategory A E T) (S : BimoduleCategory A D T)
  (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "S₀" => BimoduleCategory.underlying A D T S
local notation "LQ" => Bimodule.leftRestriction A C E D F Q₀
local notation "LQc" => BimoduleCategory.of A C D LQ
local notation "PQ" => BimoduleCategory.of A B E (compose A B C E P₀ Q₀)
local notation "LPQ" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B E D F) PQ
local notation "PLQ" => BimoduleCategory.of A B D (compose A B C D P₀ LQ)

private lemma paste_square {V : Type*} [Category* V] {a b c d e f g h : V}
    (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d) (δ : d ⟶ e)
    (p : a ⟶ f) (u : f ⟶ c) (v : f ⟶ g) (w : g ⟶ e) (x : a ⟶ h) (y : h ⟶ g)
    (hi : α ≫ β = p ≫ u) (hs : u ≫ γ ≫ δ = v ≫ w) (hn : p ≫ v = x ≫ y) :
    α ≫ β ≫ γ ≫ δ = x ≫ y ≫ w := by
  rw [← Category.assoc α β, hi, Category.assoc, hs, ← Category.assoc p v, hn, Category.assoc]

/-- 第二中間圏を制限した後の任意の指定増大による比較と、通常結合子の可換square。 -/
lemma associatorIso_secondMiddleRestriction_resolved :
    composeMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 S) ≫
      middleRestrictionResolvedMap A B E D T F PQ R S q ≫
      (associatorIso A B C E T P₀ Q₀ R₀).hom =
    (associatorIso A B C D T P₀ LQ S₀).hom ≫
      composeMap A B C T (𝟙 P) (middleRestrictionResolvedMap A C E D T F Q R S q) := by
  have hn := associatorIso_naturality A B C D T (𝟙 P) (𝟙 LQc) q
  simp only [composeMap_id] at hn
  have hs := associatorIso_secondMiddleRestriction A B C D E T F P Q R
  have h₁ := composeMap_comp A B D T
    (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 LPQ) (𝟙 S) q
  simp only [Category.comp_id, Category.id_comp] at h₁
  have h₂ := composeMap_comp A B D T (𝟙 PLQ)
    (composeLeftRestrictionIso A B C E D F P Q).hom q
    (𝟙 ((BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R))
  simp only [Category.comp_id, Category.id_comp] at h₂
  have hi := h₁.symm.trans h₂
  have hm := composeMap_comp A B C T (𝟙 P) (𝟙 P)
    (composeMap A C D T (𝟙 LQc) q) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
  simp only [Category.id_comp] at hm
  have h := paste_square _ _ _ _ _ _ _ _ _ _ hi hs hn
  dsimp only [middleRestrictionResolvedMap]
  rw [hm]
  simp only [Category.assoc]
  convert h using 1 <;> rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionResolved

/-! ## FunctorExtension（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtension.lean） -/

/-! # graph tensorの射影解像度による導来化と解像度選択比較

## 概要
graph tensorの射影解像度による導来化と解像度選択比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtension
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def dgExtensionHomotopyToDerived : ModuleHomotopyCategory A D ⥤ DerivedModuleCategory A E :=
  (dgModuleExtension A D E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

/-- 指定解像度族を用いる導来延長。元のHomのK-flat性は要求しない。 -/
def dgResolutionDerivedExtension
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  moduleDerivedResolutionFunctor A D R ⋙ dgExtensionHomotopyToDerived A D E F

/-- 標準semifree射影解像度を用いる導来延長。 -/
def dgDerivedExtension : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  dgResolutionDerivedExtension A D E F (moduleCanonicalProjectiveResolution A D)

def dgExtensionHomotopyComputation (M : ModuleCategory A D) :
    (dgExtensionHomotopyToDerived A D E F).obj ((moduleToHomotopy A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj M) :=
  (moduleHomotopyToDerivedClosed A E).mapIso
      (eqToIso (congrArg (fun G => G.obj M) (dgModuleExtension A D E F).onHomotopy_fac)) ≪≫
    (moduleToHomotopyDerivedIso A E).app ((dgModuleExtension A D E F).onClosed.obj M)

def dgResolutionDerivedExtensionComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (dgResolutionDerivedExtension A D E F R).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj (R M).obj) :=
  (dgExtensionHomotopyToDerived A D E F).mapIso (moduleDerivedResolutionComputation A D R M) ≪≫
    dgExtensionHomotopyComputation A D E F (R M).obj

def dgResolutionDerivedExtensionIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    dgResolutionDerivedExtension A D E F R ≅ dgResolutionDerivedExtension A D E F S :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A D R S)
    (dgExtensionHomotopyToDerived A D E F)

lemma dgResolutionDerivedExtensionIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    dgResolutionDerivedExtensionIso A D E F R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (dgExtensionHomotopyToDerived A D E F).map
    ((moduleDerivedResolutionIso A D R R).hom.app X) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact (dgExtensionHomotopyToDerived A D E F).map_id _

lemma dgResolutionDerivedExtensionIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    dgResolutionDerivedExtensionIso A D E F R S ≪≫ dgResolutionDerivedExtensionIso A D E F S T =
      dgResolutionDerivedExtensionIso A D E F R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (dgExtensionHomotopyToDerived A D E F).map
      ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
    (dgExtensionHomotopyToDerived A D E F).map
      ((moduleDerivedResolutionIso A D S T).hom.app X) = _
  rw [← Functor.map_comp]
  exact congrArg (dgExtensionHomotopyToDerived A D E F).map
    (NatTrans.congr_app (congrArg Iso.hom (moduleDerivedResolutionIso_trans A D R S T)) X)

/-- 指定された任意の射影解像度でも標準導来延長を計算できる。 -/
def dgDerivedExtensionResolutionComputation {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj P.obj) := by
  let R := moduleCanonicalProjectiveResolution A D
  let e := @asIso _ _ _ _ ((moduleToHomotopy A D).map ((R M).comparison P))
    ((R M).comparison_isIso_homotopy P)
  exact (dgExtensionHomotopyToDerived A D E F).mapIso
      (moduleDerivedResolutionComputation A D R M ≪≫ e) ≪≫
    dgExtensionHomotopyComputation A D E F P.obj

/-- graph tensorは射影的右加群間の準同型を保つ。相手側のflatnessは不要。 -/
lemma dgModuleExtension_projective_quasiIso
    {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E ((dgModuleExtension A D E F).onClosed.map f) :=
  dgModuleFunctor_projective_quasiIso A D E (dgModuleExtension A D E F) hM hN f hf

end SerrePositivity.DifferentialGraded
end

end FunctorExtension

/-! ## FunctorExtensionNaturality（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionNaturality.lean） -/

/-! # 射影解像度によるgraph導来延長計算の自然性

## 概要
射影解像度によるgraph導来延長計算の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

private lemma functorEqComputationNaturality {C : Type*} {T : Type*}
    [Category* C] [Category* T] {G H : C ⥤ T} (h : G = H) {M N : C} (f : M ⟶ N) :
    G.map f ≫ (eqToIso (congrArg (fun J => J.obj N) h)).hom =
      (eqToIso (congrArg (fun J => J.obj M) h)).hom ≫ H.map f := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

lemma dgExtensionHomotopyComputation_naturality {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgExtensionHomotopyToDerived A D E F).map ((moduleToHomotopy A D).map f) ≫
        (dgExtensionHomotopyComputation A D E F N).hom =
      (dgExtensionHomotopyComputation A D E F M).hom ≫
        (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) := by
  have h₂ := congrArg (moduleHomotopyToDerivedClosed A E).map
    (functorEqComputationNaturality (dgModuleExtension A D E F).onHomotopy_fac f)
  simp only [Functor.map_comp, Functor.comp_map] at h₂
  have h₃ := (moduleToHomotopyDerivedIso A E).hom.naturality
    ((dgModuleExtension A D E F).onClosed.map f)
  change (moduleHomotopyToDerivedClosed A E).map
    ((toHomotopy A (RightModule A E)).map ((dgModuleExtension A D E F).onClosed.map f)) ≫
      ((moduleToHomotopyDerivedIso A E).app ((dgModuleExtension A D E F).onClosed.obj N)).hom =
    ((moduleToHomotopyDerivedIso A E).app ((dgModuleExtension A D E F).onClosed.obj M)).hom ≫
      (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) at h₃
  have h₄ := congrArg (fun t => t ≫
    ((moduleToHomotopyDerivedIso A E).app ((dgModuleExtension A D E F).onClosed.obj N)).hom) h₂
  have h₅ := congrArg (fun t => (moduleHomotopyToDerivedClosed A E).map
    (eqToIso (congrArg (fun G => G.obj M) (dgModuleExtension A D E F).onHomotopy_fac)).hom ≫ t) h₃
  simp only [Category.assoc] at h₄ h₅
  dsimp only [dgExtensionHomotopyComputation, dgExtensionHomotopyToDerived,
    Functor.comp_map, Functor.mapIso_hom, Iso.trans_hom]
  simp only [Category.assoc]
  exact h₄.trans h₅

lemma dgResolutionDerivedExtensionComputation_naturality
    (R : ∀ N : ModuleCategory A D, ModuleProjectiveResolution A D N)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgResolutionDerivedExtension A D E F R).map ((moduleToDerived A D).map f) ≫
        (dgResolutionDerivedExtensionComputation A D E F R N).hom =
      (dgResolutionDerivedExtensionComputation A D E F R M).hom ≫
        (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
          ((R M).lift (R N) f)) := by
  let H := dgExtensionHomotopyToDerived A D E F
  have h₁ := congrArg H.map ((moduleDerivedResolutionFunctor_fac A D R).hom.naturality f)
  simp only [Functor.map_comp] at h₁
  change H.map ((moduleDerivedResolutionFunctor A D R).map ((moduleToDerived A D).map f)) ≫
      H.map (moduleDerivedResolutionComputation A D R N).hom =
    H.map (moduleDerivedResolutionComputation A D R M).hom ≫
      H.map ((moduleToHomotopy A D).map ((R M).lift (R N) f)) at h₁
  change H.map _ ≫ (H.map _ ≫ _) = (H.map _ ≫ _) ≫ _
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  exact congrArg (fun t => H.map (moduleDerivedResolutionComputation A D R M).hom ≫ t)
    (dgExtensionHomotopyComputation_naturality A D E F ((R M).lift (R N) f))

lemma dgDerivedExtensionResolutionComputation_canonical (M : ModuleCategory A D) :
    dgDerivedExtensionResolutionComputation A D E F (moduleCanonicalProjectiveResolution A D M) =
      dgResolutionDerivedExtensionComputation A D E F
        (moduleCanonicalProjectiveResolution A D) M := by
  apply Iso.ext
  change (dgExtensionHomotopyToDerived A D E F).map
      ((moduleDerivedResolutionComputation A D (moduleCanonicalProjectiveResolution A D) M).hom ≫
        (moduleToHomotopy A D).map ((moduleCanonicalProjectiveResolution A D M).comparison
          (moduleCanonicalProjectiveResolution A D M))) ≫
      (dgExtensionHomotopyComputation A D E F
        (moduleCanonicalProjectiveResolution A D M).obj).hom = _
  rw [ModuleProjectiveResolution.comparison_self, Category.comp_id]
  rfl

lemma dgDerivedExtensionResolutionComputation_inv_naturality {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    (dgDerivedExtensionResolutionComputation A D E F
        (moduleCanonicalProjectiveResolution A D M)).inv ≫
        (dgDerivedExtension A D E F).map ((moduleToDerived A D).map f) =
      (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
        ((moduleCanonicalProjectiveResolution A D M).lift
          (moduleCanonicalProjectiveResolution A D N) f)) ≫
        (dgDerivedExtensionResolutionComputation A D E F
          (moduleCanonicalProjectiveResolution A D N)).inv := by
  rw [dgDerivedExtensionResolutionComputation_canonical,
    dgDerivedExtensionResolutionComputation_canonical]
  dsimp only [dgDerivedExtension]
  have h := dgResolutionDerivedExtensionComputation_naturality A D E F
    (moduleCanonicalProjectiveResolution A D) f
  apply (cancel_mono (dgResolutionDerivedExtensionComputation A D E F
    (moduleCanonicalProjectiveResolution A D) N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionNaturality

/-! ## FunctorExtensionRepresentable（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionRepresentable.lean） -/

/-! # 導来延長の代表加群計算とHom準同型による代表比較

## 概要
導来延長の代表加群計算とHom準同型による代表比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionRepresentable
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既にホモトピー射影的な加群の恒等解像度。 -/
def moduleIdentityProjectiveResolution (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) : ModuleProjectiveResolution A D M where
  obj := M
  π := 𝟙 M
  projective := hM
  quasiIso := fun x => by rw [CategoryTheory.Functor.map_id]; infer_instance

variable (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 元のHomのflatness・有界性なしに代表加群の導来延長を計算する。 -/
def dgDerivedExtensionRepresentableIso (d : D) :
    (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
      (moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj d))) :=
  dgDerivedExtensionResolutionComputation A D E F
      (moduleIdentityProjectiveResolution A D _ (representable_homotopicallyProjective A D d)) ≪≫
    (moduleToDerived A E).mapIso (dgModuleExtensionRepresentableIso A D E F d)

/-- Hom準同型なら代表加群と制限代表加群の比較は主導来圏で同型。 -/
def representableDerivedRestrictionIso (hF : HomQuasiIso F) (d : D) :
    (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)) ≅
      (moduleToDerived A D).obj ((moduleRestriction A D E F.op).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj d)))) :=
  moduleDerivedIso A D (representableRestrictionMap A D E F d)
    (representableRestrictionMap_quasiIso A D E F hF d)

/-- Hom準同型なら、代表加群は導来延長後の導来制限と同型になる。 -/
def dgDerivedRoundTripRepresentableIso (hF : HomQuasiIso F) (d : D) :
    (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)) ≅
      (dgDerivedRestriction A D E F).obj
        ((dgDerivedExtension A D E F).obj
          ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)))) :=
  representableDerivedRestrictionIso A D E F hF d ≪≫
    (eqToIso (congrArg (fun G => G.obj
      (ForgetEnrichment.of (Complex A) (representable A (F.obj d))))
      (dgDerivedRestriction_fac A D E F))).symm ≪≫
    (dgDerivedRestriction A D E F).mapIso (dgDerivedExtensionRepresentableIso A D E F d).symm

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionRepresentable
