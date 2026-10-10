module

public import SerrePositivity.HomologicalAlgebra.Resolution

/-! # コチェイン分解による導来関手の計算の自然性

分解の間の射が零次ホモロジーで指定した加群の射を誘導すれば、
その射に加法関手を施して得るホモロジーの射は、左導来関手の標準の射と一致する。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 自然数添字への制限における余サイクルの比較。 -/
noncomputable abbrev toChainOpcyclesIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (toChain K).opcycles n ≅ K.opcycles (-(n : ℤ)) :=
  K.restrictionOpcyclesIso embUp (i := n + 1) (j := n) (hi := by simp [ChainComplex.prev])
    (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ)) (hi' := by simp) (hj' := by simp)
    (hi'' := by simp [CochainComplex.prev]; omega)

@[reassoc]
lemma toChainHomologyIso_hom_homologyι (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) (n : ℕ) :
    (toChainHomologyIso K hK n).hom ≫ K.homologyι (-(n : ℤ)) =
      (toChain K).homologyι n ≫ (toChainOpcyclesIso K n).hom := by
  cases n with
  | zero =>
    have := K.isIso_homologyι 0 1 (by simp) (d_zero_one_eq_zero K hK)
    simp [toChainHomologyIso, toChainHomologyIsoZero, toChainOpcyclesIso]
  | succ n =>
    exact restrictionHomologyIso_hom_homologyι ..

@[reassoc]
lemma toChainOpcyclesIso_hom_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℕ) :
    opcyclesMap (restrictionMap f embUp) n ≫ (toChainOpcyclesIso L n).hom =
      (toChainOpcyclesIso K n).hom ≫ opcyclesMap f (-(n : ℤ)) := by
  apply (cancel_epi ((toChain K).pOpcycles n)).mp
  simp only [p_opcyclesMap_assoc, toChainOpcyclesIso,
    pOpcycles_restrictionOpcyclesIso_hom, pOpcycles_restrictionOpcyclesIso_hom_assoc,
    p_opcyclesMap]
  rw [restrictionMap_f' f embUp (by simp : embUp.f n = -(n : ℤ))]
  simp

/-- ホモロジーの添字変換は、分解の射と可換である。 -/
@[reassoc]
lemma toChainHomologyIso_hom_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) (hL : ∀ q : ℤ, 0 < q → IsZero (L.X q)) (n : ℕ) :
    homologyMap (restrictionMap f embUp) n ≫ (toChainHomologyIso L hL n).hom =
      (toChainHomologyIso K hK n).hom ≫ homologyMap f (-(n : ℤ)) := by
  apply (cancel_mono (L.homologyι (-(n : ℤ)))).mp
  simp only [Category.assoc, toChainHomologyIso_hom_homologyι,
    homologyι_naturality, homologyι_naturality_assoc,
    toChainHomologyIso_hom_homologyι_assoc, toChainOpcyclesIso_hom_naturality]

/-- 分解の零次ホモロジーでの両立から、自然数添字の増大射との両立を得る。 -/
lemma IsResolutionOf.restrictionMap_π_f_zero
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} {X Y : ModuleCat.{u} R}
    (hK : IsResolutionOf K X) (hL : IsResolutionOf L Y) (f : K ⟶ L) (g : X ⟶ Y)
    (h : homologyMap f 0 ≫ hL.homologyZeroIso.hom = hK.homologyZeroIso.hom ≫ g) :
    (restrictionMap f embUp).f 0 ≫ hL.π.f 0 = hK.π.f 0 ≫ g := by
  have he : opcyclesMap (restrictionMap f embUp) 0 ≫ hL.opcyclesIso.hom =
      hK.opcyclesIso.hom ≫ g := by
    apply (cancel_epi ((toChain K).homologyι 0)).mp
    simp only [IsResolutionOf.opcyclesIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      ← homologyι_naturality_assoc, Category.assoc]
    simp only [IsIso.hom_inv_id_assoc]
    have hn : homologyMap (restrictionMap f embUp) 0 ≫ (toChainHomologyIsoZero L hL.isZero_X).hom =
        (toChainHomologyIsoZero K hK.isZero_X).hom ≫ homologyMap f 0 := by
      simpa [toChainHomologyIso] using
        toChainHomologyIso_hom_naturality f hK.isZero_X hL.isZero_X 0
    rw [← Category.assoc, hn, Category.assoc, h]
  rw [IsResolutionOf.π_f_zero, IsResolutionOf.π_f_zero, ← Category.assoc,
    ← p_opcyclesMap, Category.assoc, he, Category.assoc]

/-- 関手と添字制限の比較は、複体の射と可換である。 -/
@[reassoc]
lemma mapRestrictionIso_hom_naturality (G : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [G.Additive]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    (G.mapHomologicalComplex _).map (restrictionMap f embUp) ≫ (mapRestrictionIso G L).hom =
      (mapRestrictionIso G K).hom ≫ restrictionMap ((G.mapHomologicalComplex _).map f) embUp := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp [mapRestrictionIso]

/-- コチェイン分解で計算した射は、左導来関手の標準の射と一致する。 -/
@[reassoc]
lemma leftDerivedIsoCochain_hom_naturality
    (G : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [G.Additive]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} {X Y : ModuleCat.{u} R}
    (hK : IsResolutionOf K X) (hL : IsResolutionOf L Y) (f : K ⟶ L) (g : X ⟶ Y)
    (h : homologyMap f 0 ≫ hL.homologyZeroIso.hom = hK.homologyZeroIso.hom ≫ g) (i : ℕ) :
    (G.leftDerived i).map g ≫ (leftDerivedIsoCochain G hL i).hom =
      (leftDerivedIsoCochain G hK i).hom ≫
        homologyMap ((G.mapHomologicalComplex _).map f) (-(i : ℤ)) := by
  have hn := ProjectiveResolution.isoLeftDerivedObj_hom_naturality g
    hK.toProjectiveResolution hL.toProjectiveResolution (restrictionMap f embUp)
    (hK.restrictionMap_π_f_zero hL f g h) G i
  have hr := congrArg ((homologyFunctor (ModuleCat S) (.down ℕ) i).map)
    (mapRestrictionIso_hom_naturality G f)
  simp only [CategoryTheory.Functor.map_comp] at hr
  have ht := toChainHomologyIso_hom_naturality ((G.mapHomologicalComplex _).map f)
    (fun j hj ↦ G.map_isZero (hK.isZero_X j hj))
    (fun j hj ↦ G.map_isZero (hL.isZero_X j hj)) i
  simp only [leftDerivedIsoCochain, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (toChainHomologyIso _ _ i).hom]
  erw [hr]
  simp only [Category.assoc]
  erw [ht]

/-- 関手と添字制限の比較は、関手の間の自然変換とも可換である。 -/
@[reassoc]
lemma mapRestrictionIso_natTrans (F G : ModuleCat.{u} R ⥤ ModuleCat.{u} S)
    [F.Additive] [G.Additive] (α : F ⟶ G) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (NatTrans.mapHomologicalComplex α _).app (toChain K) ≫ (mapRestrictionIso G K).hom =
      (mapRestrictionIso F K).hom ≫
        restrictionMap ((NatTrans.mapHomologicalComplex α _).app K) embUp := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp [mapRestrictionIso]
  rfl

/-- コチェイン分解による計算は、加法関手の間の自然変換と可換である。 -/
@[reassoc]
lemma leftDerivedIsoCochain_natTrans
    (F G : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] [G.Additive] (α : F ⟶ G)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {X : ModuleCat.{u} R}
    (hK : IsResolutionOf K X) (i : ℕ) :
    (NatTrans.leftDerived α i).app X ≫ (leftDerivedIsoCochain G hK i).hom =
      (leftDerivedIsoCochain F hK i).hom ≫
        homologyMap ((NatTrans.mapHomologicalComplex α _).app K) (-(i : ℤ)) := by
  have hn := hK.toProjectiveResolution.leftDerived_app_eq α i
  have hr := congrArg ((homologyFunctor (ModuleCat S) (.down ℕ) i).map)
    (mapRestrictionIso_natTrans F G α K)
  simp only [CategoryTheory.Functor.map_comp] at hr
  have ht := toChainHomologyIso_hom_naturality ((NatTrans.mapHomologicalComplex α _).app K)
    (fun j hj ↦ F.map_isZero (hK.isZero_X j hj))
    (fun j hj ↦ G.map_isZero (hK.isZero_X j hj)) i
  simp only [leftDerivedIsoCochain, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom]
  rw [hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc _ _ (toChainHomologyIso _ _ i).hom]
  erw [hr]
  simp only [Category.assoc]
  erw [ht]

end SerrePositivity
