module

public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology
public import SerrePositivity.HomologicalAlgebra.Resolution
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # 線形双対複体と Ext

## 概要

加群の chain 複体の線形双対 cochain 複体（`chainLinearYonedaFunctor`、ℤ 添字の `cochainLinearDualFunctor`）を作り、入射的な係数では双対が完全でホモロジーと可換すること、射影的な項では係数関手が完全であること、零次の双対コホモロジーは仮定なしで計算できること、指定した射影分解による Mathlib の Ext の計算の自然性、写像錐の双対が逆向きの双対写像の錐であることを示す。

## 方針

双対は `linearYoneda` を ModuleCat に値を取る形で使う。完全性は入射的・射影的な対象の Hom の完全性から。

## 規約

`linearYonedaModule_preservesHomology` 系は Mathlib の `preservesHomology_preadditiveYonedaObj_of_injective`（AddCommGrp 値）で置き換える候補。

## 使われ方

局所コホモロジー（HomologicalAlgebra/Ext/LocalCohomology）、Koszul の線形双対性。
-/

@[expose] public noncomputable section

universe u

section ChainLinearYonedaPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]
variable {α : Type*} [AddRightCancelSemigroup α] [One α]

/-- The cochain complex Hom(K,-), naturally in the coefficient module. -/
def chainLinearYonedaFunctor (K : ChainComplex (ModuleCat.{u} R) α) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) α where
  obj M := K.linearYonedaObj R M
  map f :=
    { f := fun i => ModuleCat.ofHom (Linear.rightComp R (K.X i) f)
      comm' := by
        intro i j hij
        apply ModuleCat.hom_ext
        ext g
        rfl }
  map_id M := by
    ext i g
    rfl
  map_comp f g := by
    ext i h
    rfl

/-- Unoppositing a chain map commutes with its cohomology comparison. -/
lemma chainHomologyUnop_hom_naturality
    {K L : ChainComplex (ModuleCat.{u} R)ᵒᵖ ℕ} (f : K ⟶ L) (i : ℕ) :
    homologyMap ((unopFunctor (ModuleCat R) (.down ℕ)).map f.op) i ≫
        (homologyUnop K i).hom =
      (homologyUnop L i).hom ≫ (homologyMap f i).unop := by
  let ψ := (unopFunctor (ModuleCat R) (.down ℕ)).map f.op
  have h := congrArg Quiver.Hom.unop (homologyOp_hom_naturality ψ i)
  change (homologyUnop L i).hom ≫ (homologyMap f i).unop =
    homologyMap ψ i ≫ (homologyUnop K i).hom at h
  exact h.symm

/-- The inverse unop homology comparison is natural as well. -/
lemma chainHomologyUnop_inv_naturality
    {K L : ChainComplex (ModuleCat.{u} R)ᵒᵖ ℕ} (f : K ⟶ L) (i : ℕ) :
    (homologyMap f i).unop ≫ (homologyUnop K i).inv =
      (homologyUnop L i).inv ≫
        homologyMap ((unopFunctor (ModuleCat R) (.down ℕ)).map f.op) i := by
  apply (cancel_epi (homologyUnop L i).hom).mp
  rw [← Category.assoc, ← chainHomologyUnop_hom_naturality f i]
  simp

/-- Precomposition by a chain map gives a natural morphism of dual cochain functors. -/
def chainLinearYonedaMap {K L : ChainComplex (ModuleCat.{u} R) α} (f : K ⟶ L) :
    chainLinearYonedaFunctor L ⟶ chainLinearYonedaFunctor K where
  app M :=
    { f := fun i => ModuleCat.ofHom (Linear.leftComp R M (f.f i))
      comm' := by
        intro i j hij
        apply ModuleCat.hom_ext
        ext g
        change (K.d j i ≫ f.f i) ≫ g = (f.f j ≫ L.d j i) ≫ g
        rw [f.comm] }
  naturality {M N} g := by
    ext i h
    rfl

@[simp] lemma chainLinearYonedaMap_id (K : ChainComplex (ModuleCat.{u} R) α) :
    chainLinearYonedaMap (𝟙 K) = 𝟙 (chainLinearYonedaFunctor K) := by
  ext M i g
  rfl

lemma chainLinearYonedaMap_comp {K L P : ChainComplex (ModuleCat.{u} R) α}
    (f : K ⟶ L) (g : L ⟶ P) :
    chainLinearYonedaMap (f ≫ g) = chainLinearYonedaMap g ≫ chainLinearYonedaMap f := by
  ext M i h
  rfl

end SerrePositivity

end ChainLinearYonedaPart

section InjectiveLinearYonedaPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The module-valued linear Yoneda functor preserves limits. -/
instance linearYonedaModule_preservesLimits (J : ModuleCat.{u} R) :
    PreservesLimits ((linearYoneda R (ModuleCat.{u} R)).obj J) := by
  have : PreservesLimits (((linearYoneda R (ModuleCat.{u} R)).obj J) ⋙
      forget (ModuleCat.{u} R)) := by
    change PreservesLimits (yoneda.obj J)
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

/-- Injective coefficients make linear duality preserve epimorphisms as well. -/
instance linearYonedaModule_preservesEpimorphisms (J : ModuleCat.{u} R) [Injective J] :
    ((linearYoneda R (ModuleCat.{u} R)).obj J).PreservesEpimorphisms := by
  let : (yoneda.obj J).PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_yoneda_obj J).mp inferInstance
  have : (((linearYoneda R (ModuleCat.{u} R)).obj J) ⋙
      forget (ModuleCat.{u} R)).PreservesEpimorphisms := by
    change (yoneda.obj J).PreservesEpimorphisms
    infer_instance
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    ((linearYoneda R (ModuleCat.{u} R)).obj J) (forget (ModuleCat.{u} R))

/-- Linear duality with injective coefficients preserves actual homology. -/
instance linearYonedaModule_preservesHomology (J : ModuleCat.{u} R) [Injective J] :
    ((linearYoneda R (ModuleCat.{u} R)).obj J).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Injective coefficients identify dual cohomology with the actual linear dual of homology. -/
def injectiveChainLinearYonedaHomologyIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) :
    (K.linearYonedaObj R J).homology i ≅ ModuleCat.of R (K.homology i ⟶ J) :=
  (K.op.sc i).mapHomologyIso ((linearYoneda R (ModuleCat.{u} R)).obj J) ≪≫
    ((linearYoneda R (ModuleCat.{u} R)).obj J).mapIso (homologyOp K i)

/-- This duality respects the actual dual chain map, including its contravariant direction. -/
lemma injectiveChainLinearYonedaHomologyIso_naturality
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) :
    homologyMap ((chainLinearYonedaMap f).app J) i ≫
        (injectiveChainLinearYonedaHomologyIso K J i).hom =
      (injectiveChainLinearYonedaHomologyIso L J i).hom ≫
        ((linearYoneda R (ModuleCat.{u} R)).obj J).map (homologyMap f i).op := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  let ψ := (opFunctor (ModuleCat.{u} R) (.down ℕ)).map f.op
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (ModuleCat.{u} R)ᵒᵖ (.up ℕ) i).map ψ) F
  change homologyMap ((chainLinearYonedaMap f).app J) i ≫
      ((K.op.sc i).mapHomologyIso F).hom =
    ((L.op.sc i).mapHomologyIso F).hom ≫ F.map (homologyMap ψ i) at h
  change _ ≫ (((K.op.sc i).mapHomologyIso F).hom ≫ F.map (homologyOp K i).hom) =
    (((L.op.sc i).mapHomologyIso F).hom ≫ F.map (homologyOp L i).hom) ≫ _
  rw [← Category.assoc, h, Category.assoc, ← F.map_comp,
    homologyOp_hom_naturality, F.map_comp, Category.assoc]

/-- Zero original homology maps yield zero dual cohomology maps for injective coefficients. -/
lemma chainLinearYonedaMap_homology_eq_zero_of_injective
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hf : homologyMap f i = 0) :
    homologyMap ((chainLinearYonedaMap f).app J) i = 0 := by
  apply (cancel_mono (injectiveChainLinearYonedaHomologyIso K J i).hom).mp
  rw [zero_comp, injectiveChainLinearYonedaHomologyIso_naturality, hf]
  simp only [op_zero, linearYoneda_obj_map, unop_zero, Preadditive.IsIso.comp_left_eq_zero]
  ext g x
  change g (0 : L.homology i) = 0
  exact (g : L.homology i ⟶ J).hom.map_zero

end SerrePositivity

end InjectiveLinearYonedaPart

section ProjectiveLinearCoyonedaPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Linear Hom out of any fixed module preserves limits in its coefficient variable. -/
instance linearCoyonedaModule_preservesLimits (P : ModuleCat.{u} R) :
    PreservesLimits ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) := by
  have : PreservesLimits (((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) ⋙
      forget (ModuleCat.{u} R)) := by
    change PreservesLimits (coyoneda.obj (op P))
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

/-- Projectivity makes linear Hom preserve epimorphisms of coefficients. -/
instance linearCoyonedaModule_preservesEpimorphisms
    (P : ModuleCat.{u} R) [Projective P] :
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)).PreservesEpimorphisms := by
  let : (coyoneda.obj (op P)).PreservesEpimorphisms :=
    (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj P).mp inferInstance
  have : (((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) ⋙
      forget (ModuleCat.{u} R)).PreservesEpimorphisms := by
    change (coyoneda.obj (op P)).PreservesEpimorphisms
    infer_instance
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) (forget (ModuleCat.{u} R))

/-- Linear Hom out of a projective module preserves homology of coefficient short complexes. -/
instance linearCoyonedaModule_preservesHomology (P : ModuleCat.{u} R) [Projective P] :
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Linear Hom out of a projective module preserves finite colimits of coefficients. -/
instance linearCoyonedaModule_preservesFiniteColimits
    (P : ModuleCat.{u} R) [Projective P] :
    PreservesFiniteColimits ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The entire dual cochain coefficient functor preserves finite limits. -/
instance chainLinearYonedaFunctor_preservesFiniteLimits
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    PreservesFiniteLimits (chainLinearYonedaFunctor K) where
  preservesFiniteLimits J _ _ :=
    preservesLimitsOfShape_of_eval _ (fun i => by
      change PreservesLimitsOfShape J ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (K.X i)))
      infer_instance)

/-- Degreewise projective chain complexes give exact dual cochain coefficient functors. -/
instance chainLinearYonedaFunctor_preservesFiniteColimits
    (K : ChainComplex (ModuleCat.{u} R) ℕ) [∀ i, Projective (K.X i)] :
    PreservesFiniteColimits (chainLinearYonedaFunctor K) where
  preservesFiniteColimits J _ _ :=
    preservesColimitsOfShape_of_eval _ (fun i => by
      change PreservesColimitsOfShape J ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (K.X i)))
      infer_instance)

end SerrePositivity

end ProjectiveLinearCoyonedaPart

section ChainLinearYonedaZeroPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- At the initial cochain degree, linear duality preserves homology for all coefficients. -/
lemma chainLinearYoneda_preserves_zero_leftHomology
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (J : ModuleCat.{u} R) :
    ((linearYoneda R (ModuleCat.{u} R)).obj J).PreservesLeftHomologyOf (K.op.sc 0) := by
  apply Functor.preservesLeftHomology_of_zero_f
  change K.op.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  apply K.op.shape
  change ¬ ((ComplexShape.up ℕ).prev 0 + 1 = 0)
  omega

/-- The same boundary condition also preserves right homology data at degree zero. -/
lemma chainLinearYoneda_preserves_zero_rightHomology
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (J : ModuleCat.{u} R) :
    ((linearYoneda R (ModuleCat.{u} R)).obj J).PreservesRightHomologyOf (K.op.sc 0) := by
  apply Functor.preservesRightHomology_of_zero_f
  change K.op.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  apply K.op.shape
  change ¬ ((ComplexShape.up ℕ).prev 0 + 1 = 0)
  omega

/-- Degree-zero cohomology of the dual is Hom from degree-zero homology, for any coefficients. -/
def chainLinearYonedaZeroHomologyIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (J : ModuleCat.{u} R) :
    (K.linearYonedaObj R J).homology 0 ≅ ModuleCat.of R (K.homology 0 ⟶ J) := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  have : F.PreservesLeftHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology K J
  letI : ((K.op.sc 0).map F).HasHomology := CategoryWithHomology.hasHomology _
  exact (K.op.sc 0).mapHomologyIso F ≪≫ F.mapIso (homologyOp K 0)

/-- The zero-degree comparison is natural in chain maps without injective coefficients. -/
lemma chainLinearYonedaZeroHomologyIso_chain_naturality
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (J : ModuleCat.{u} R) :
    homologyMap ((chainLinearYonedaMap f).app J) 0 ≫
        (chainLinearYonedaZeroHomologyIso K J).hom =
      (chainLinearYonedaZeroHomologyIso L J).hom ≫
        ((linearYoneda R (ModuleCat.{u} R)).obj J).map (homologyMap f 0).op := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  have : F.PreservesLeftHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology K J
  have : F.PreservesLeftHomologyOf (L.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology L J
  let : ((K.op.sc 0).map F).HasHomology := CategoryWithHomology.hasHomology _
  let : ((L.op.sc 0).map F).HasHomology := CategoryWithHomology.hasHomology _
  let ψ := (opFunctor (ModuleCat.{u} R) (.down ℕ)).map f.op
  have h := ShortComplex.mapHomologyIso_hom_naturality
    (S₁ := L.op.sc 0) (S₂ := K.op.sc 0)
    ((shortComplexFunctor (ModuleCat.{u} R)ᵒᵖ (.up ℕ) 0).map ψ) F
  change homologyMap ((chainLinearYonedaMap f).app J) 0 ≫
      ((K.op.sc 0).mapHomologyIso F).hom =
    ((L.op.sc 0).mapHomologyIso F).hom ≫ F.map (homologyMap ψ 0) at h
  change _ ≫ (((K.op.sc 0).mapHomologyIso F).hom ≫ F.map (homologyOp K 0).hom) =
    (((L.op.sc 0).mapHomologyIso F).hom ≫ F.map (homologyOp L 0).hom) ≫ _
  rw [← Category.assoc, h, Category.assoc, ← F.map_comp,
    homologyOp_hom_naturality, F.map_comp, Category.assoc]

/-- The zero-degree comparison is also natural in arbitrary coefficient morphisms. -/
lemma chainLinearYonedaZeroHomologyIso_coefficient_naturality
    (K : ChainComplex (ModuleCat.{u} R) ℕ) {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    homologyMap ((chainLinearYonedaFunctor K).map f) 0 ≫
        (chainLinearYonedaZeroHomologyIso K J').hom =
      (chainLinearYonedaZeroHomologyIso K J).hom ≫
        ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (K.homology 0))).map f := by
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  let G := (linearYoneda R (ModuleCat.{u} R)).obj J'
  let τ : F ⟶ G := (linearYoneda R (ModuleCat.{u} R)).map f
  have : F.PreservesLeftHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology K J
  have : G.PreservesLeftHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_leftHomology K J'
  let : ((K.op.sc 0).map F).HasHomology := CategoryWithHomology.hasHomology _
  let : ((K.op.sc 0).map G).HasHomology := CategoryWithHomology.hasHomology _
  have : F.PreservesRightHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_rightHomology K J
  have : G.PreservesRightHomologyOf (K.op.sc 0) :=
    chainLinearYoneda_preserves_zero_rightHomology K J'
  have h := ShortComplex.homologyMap_mapNatTrans (K.op.sc 0) τ
  change homologyMap ((chainLinearYonedaFunctor K).map f) 0 =
    ((K.op.sc 0).mapHomologyIso F).hom ≫ τ.app (K.op.homology 0) ≫
      ((K.op.sc 0).mapHomologyIso G).inv at h
  change _ ≫ (((K.op.sc 0).mapHomologyIso G).hom ≫ G.map (homologyOp K 0).hom) =
    (((K.op.sc 0).mapHomologyIso F).hom ≫ F.map (homologyOp K 0).hom) ≫
      τ.app (op (K.homology 0))
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← τ.naturality]

/-- Zero dual cohomology is the represented Hom functor, naturally in all coefficients. -/
def chainLinearYonedaZeroHomologyNatIso (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    chainLinearYonedaFunctor K ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      (linearCoyoneda R (ModuleCat.{u} R)).obj (op (K.homology 0)) :=
  NatIso.ofComponents (fun J => chainLinearYonedaZeroHomologyIso K J)
    (fun f => chainLinearYonedaZeroHomologyIso_coefficient_naturality K f)

end SerrePositivity

end ChainLinearYonedaZeroPart

section ProjectiveExtNaturalityPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Ext computed by a specified projective resolution is natural in the coefficient module. -/
lemma projectiveResolutionIsoExt_naturality {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (i : ℕ) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Ext R (ModuleCat R) i).obj (op X)).map f ≫ (P.isoExt i N).hom =
      (P.isoExt i M).hom ≫
        homologyMap ((chainLinearYonedaFunctor P.complex).map f) i := by
  let FM := ((linearYoneda R (ModuleCat R)).obj M).rightOp
  let FN := ((linearYoneda R (ModuleCat R)).obj N).rightOp
  let β : FN ⟶ FM := ((linearYoneda R (ModuleCat R)).map f).rightOp
  let KM := (FM.mapHomologicalComplex (.down ℕ)).obj P.complex
  let KN := (FN.mapHomologicalComplex (.down ℕ)).obj P.complex
  let b : KN ⟶ KM := (NatTrans.mapHomologicalComplex β (.down ℕ)).app P.complex
  change ((NatTrans.leftDerived β i).app X).unop ≫
      ((P.isoLeftDerivedObj FN i).inv.unop ≫ (homologyUnop KN i).inv) =
    ((P.isoLeftDerivedObj FM i).inv.unop ≫ (homologyUnop KM i).inv) ≫
      homologyMap ((chainLinearYonedaFunctor P.complex).map f) i
  rw [P.leftDerived_app_eq β i]
  simp only [unop_comp, Category.assoc]
  have hc : (P.isoLeftDerivedObj FN i).hom.unop ≫ (P.isoLeftDerivedObj FN i).inv.unop =
      𝟙 _ := by simp only [← unop_comp, Iso.inv_hom_id, unop_id]
  rw [← Category.assoc (P.isoLeftDerivedObj FN i).hom.unop
    (P.isoLeftDerivedObj FN i).inv.unop (homologyUnop KN i).inv, hc, Category.id_comp]
  have hn := chainHomologyUnop_inv_naturality b i
  change (homologyMap b i).unop ≫ (homologyUnop KN i).inv =
    (homologyUnop KM i).inv ≫
      homologyMap ((chainLinearYonedaFunctor P.complex).map f) i at hn
  erw [hn]

/-- A functorial Ext computation, rather than unrelated isomorphisms for individual modules. -/
def projectiveResolutionExtNatIso {X : ModuleCat.{u} R} (P : ProjectiveResolution X) (i : ℕ) :
    (Ext R (ModuleCat R) i).obj (op X) ≅
      chainLinearYonedaFunctor P.complex ⋙ homologyFunctor (ModuleCat R) (.up ℕ) i :=
  NatIso.ofComponents (fun M => P.isoExt i M)
    (fun f => projectiveResolutionIsoExt_naturality P i f)

/-- The computation respects any augmented lift of a morphism in Ext's first argument. -/
lemma projectiveResolutionIsoExt_first_naturality
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (M : ModuleCat.{u} R) (i : ℕ) :
    ((Ext R (ModuleCat R) i).map f.op).app M ≫ (P.isoExt i M).hom =
      (Q.isoExt i M).hom ≫ homologyMap ((chainLinearYonedaMap φ).app M) i := by
  let F := ((linearYoneda R (ModuleCat R)).obj M).rightOp
  let KP := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  let KQ := (F.mapHomologicalComplex (.down ℕ)).obj Q.complex
  let b : KP ⟶ KQ := (F.mapHomologicalComplex (.down ℕ)).map φ
  have hn := congrArg Quiver.Hom.unop
    (ProjectiveResolution.isoLeftDerivedObj_inv_naturality f P Q φ hφ F i)
  change ((F.leftDerived i).map f).unop ≫ (P.isoLeftDerivedObj F i).inv.unop =
    (Q.isoLeftDerivedObj F i).inv.unop ≫ (homologyMap b i).unop at hn
  change ((F.leftDerived i).map f).unop ≫
      ((P.isoLeftDerivedObj F i).inv.unop ≫ (homologyUnop KP i).inv) =
    ((Q.isoLeftDerivedObj F i).inv.unop ≫ (homologyUnop KQ i).inv) ≫
      homologyMap ((chainLinearYonedaMap φ).app M) i
  rw [← Category.assoc, hn, Category.assoc]
  have hu := chainHomologyUnop_inv_naturality b i
  change (homologyMap b i).unop ≫ (homologyUnop KP i).inv =
    (homologyUnop KQ i).inv ≫ homologyMap ((chainLinearYonedaMap φ).app M) i at hu
  rw [hu]
  simp only [Category.assoc]

end SerrePositivity

end ProjectiveExtNaturalityPart

section ProjectiveResolutionInjectiveAcyclicPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
variable {R : Type u} [CommRing R]

/-- Positive homology of any actual projective resolution vanishes. -/
lemma projectiveResolution_positive_homology_isZero {X : ModuleCat.{u} R}
    (P : ProjectiveResolution X) (i : ℕ) (hi : 0 < i) :
    IsZero (P.complex.homology i) := by
  apply IsZero.of_iso _ (isoOfQuasiIsoAt P.π i)
  exact isZero_single_obj_homology (.down ℕ) 0 X i (Nat.ne_of_gt hi)

/-- Dualizing a projective resolution into an injective coefficient module
has no positive cohomology, without any regular-sequence assumption. -/
lemma projectiveResolution_injective_dual_positive_homology_isZero
    {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hi : 0 < i) :
    IsZero (((chainLinearYonedaFunctor P.complex).obj J).homology i) := by
  apply IsZero.of_iso _ (injectiveChainLinearYonedaHomologyIso P.complex J i)
  exact ((linearYoneda R (ModuleCat.{u} R)).obj J).map_isZero
    (projectiveResolution_positive_homology_isZero P i hi).op

end SerrePositivity

end ProjectiveResolutionInjectiveAcyclicPart

section CochainLinearDualPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Reversing integer degrees converts a cochain complex to a chain complex. -/
def integerNegEmbedding : ComplexShape.Embedding (.down ℤ) (.up ℤ) :=
  .mk' _ _ (fun i => 0 - i) (fun _ _ h => by dsimp at h; omega) (by dsimp; omega)

instance integerNegEmbedding_isRelIff : integerNegEmbedding.IsRelIff := by
  dsimp [integerNegEmbedding]
  infer_instance

/-- The nonnegative degrees, embedded without changing their integer value. -/
def nonnegativeCochainEmbedding : ComplexShape.Embedding (.up ℕ) (.up ℤ) :=
  .mk' _ _ (fun n => (n : ℤ)) (fun _ _ h => by dsimp at h; omega) (by dsimp; omega)

instance nonnegativeCochainEmbedding_isRelIff : nonnegativeCochainEmbedding.IsRelIff := by
  dsimp [nonnegativeCochainEmbedding]
  infer_instance

/-- The dual cochain complex has Hom(K^(-i),M) in integer degree i. -/
abbrev cochainLinearDualFunctor (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  chainLinearYonedaFunctor (K.restriction integerNegEmbedding)

/-- A complex map induces contravariant precomposition on its integer-indexed dual. -/
abbrev cochainLinearDualMap {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    cochainLinearDualFunctor L ⟶ cochainLinearDualFunctor K :=
  chainLinearYonedaMap (restrictionMap f integerNegEmbedding)

/-- Restricting the integer dual recovers the actual nonnegative dual used for Ext. -/
def cochainLinearDualNonnegativeIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) :
    ((cochainLinearDualFunctor K).obj M).restriction nonnegativeCochainEmbedding ≅
      (chainLinearYonedaFunctor (toChain K)).obj M :=
  Iso.refl _

/-- The restriction comparison is natural in every coefficient map. -/
def cochainLinearDualNonnegativeNatIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainLinearDualFunctor K ⋙ nonnegativeCochainEmbedding.restrictionFunctor (ModuleCat R) ≅
      chainLinearYonedaFunctor (toChain K) :=
  NatIso.ofComponents (cochainLinearDualNonnegativeIso K) (fun _ => rfl)

/-- The differential of the dual is actual precomposition, with no hidden sign convention. -/
lemma cochainLinearDual_d_apply (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) (i j : ℤ) (f : K.X (0 - i) ⟶ M) :
    (((cochainLinearDualFunctor K).obj M).d i j).hom f = K.d (0 - j) (0 - i) ≫ f := rfl

end SerrePositivity

end CochainLinearDualPart

section MappingConeLinearDualPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- Morphisms from a cone term are pairs of morphisms from its two summands. -/
def mappingConeTargetHomEquiv (M : ModuleCat.{u} R) (q : ℤ) :
    (((CochainComplex.mappingCone φ).X q) ⟶ M) ≃ₗ[R]
      ((K.X (q + 1) ⟶ M) × (L.X q ⟶ M)) where
  toFun f := ⟨inlX φ (q + 1) q rfl ≫ f, inrX φ q ≫ f⟩
  invFun f := fstX φ q (q + 1) rfl ≫ f.1 + sndX φ q ≫ f.2
  left_inv f := by
    apply ext_from_X φ (q + 1) q rfl <;> simp
  right_inv f := by simp
  map_add' f g := by simp [Preadditive.comp_add]
  map_smul' a f := by simp [Linear.comp_smul]

/-- The first dual component is restriction to the shifted source summand. -/
@[simp] lemma mappingConeTargetHomEquiv_fst (M : ModuleCat.{u} R) (q : ℤ)
    (f : ((CochainComplex.mappingCone φ).X q) ⟶ M) :
    (mappingConeTargetHomEquiv φ M q f).1 = inlX φ (q + 1) q rfl ≫ f := rfl

/-- The second dual component is restriction to the target summand. -/
@[simp] lemma mappingConeTargetHomEquiv_snd (M : ModuleCat.{u} R) (q : ℤ)
    (f : ((CochainComplex.mappingCone φ).X q) ⟶ M) :
    (mappingConeTargetHomEquiv φ M q f).2 = inrX φ q ≫ f := rfl

end SerrePositivity

end MappingConeLinearDualPart

section CochainLinearDualConePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- Changing the label of the shifted source summand only transports its source object. -/
lemma mappingCone_inlX_cast (q r : ℤ) (h : q + 1 = r) :
    (K.XIsoOfEq h).inv ≫ inlX φ (q + 1) q rfl = inlX φ r q h := by
  subst r
  simp

/-- Swapping the dual summands and negating the old source gives the shifted cone comparison. -/
def cochainLinearDualConeShiftTermIso (M : ModuleCat.{u} R) (i : ℤ) :
    (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).X i ≅
      (CochainComplex.mappingCone ((cochainLinearDualMap φ).app M)).X i := by
  let E := mappingConeTargetHomEquiv φ M (0 - (i + 1))
  let e : (K.X (0 - (i + 1) + 1) ⟶ M) ≃ₗ[R] (K.X (0 - i) ⟶ M) :=
    Linear.homCongr R (K.XIsoOfEq (by omega)) (Iso.refl M)
  exact (E.trans ((LinearEquiv.prodComm R _ _).trans
    ((LinearEquiv.refl R _).prodCongr (e.trans (LinearEquiv.neg R))))).toModuleIso ≪≫
      (mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).symm

/-- The first comparison coordinate is the old target restriction. -/
lemma cochainLinearDualConeShiftTermIso_fst (M : ModuleCat.{u} R) (i : ℤ)
    (f : (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).X i) :
    ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).hom
      ((cochainLinearDualConeShiftTermIso φ M i).hom f)).1 =
      inrX φ (0 - (i + 1)) ≫ f := by
  simp only [CochainComplex.shiftFunctor_obj_X']
  change ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).hom
    ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).inv _)).1 = _
  rw [ModuleCat.hom_inv_apply]
  rfl

/-- The second comparison coordinate is the negative old source restriction. -/
lemma cochainLinearDualConeShiftTermIso_snd (M : ModuleCat.{u} R) (i : ℤ)
    (f : (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).X i) :
    ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).hom
      ((cochainLinearDualConeShiftTermIso φ M i).hom f)).2 =
      -(inlX φ (0 - i) (0 - (i + 1)) (by change 0 - (i + 1) + 1 = 0 - i; omega) ≫ f) := by
  simp only [CochainComplex.shiftFunctor_obj_X']
  change ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).hom
    ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).inv _)).2 = _
  rw [ModuleCat.hom_inv_apply]
  change -(((K.XIsoOfEq (show 0 - (i + 1) + 1 = 0 - i by omega)).inv ≫
    (inlX φ (0 - (i + 1) + 1) (0 - (i + 1)) rfl ≫ f)) ≫ 𝟙 M) = _
  rw [Category.comp_id, ← Category.assoc, mappingCone_inlX_cast]

/-- The shift by one negates the reversed precomposition differential. -/
lemma cochainLinearDualShiftOne_d_apply (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) (i j : ℤ) (f : P.X (0 - (i + 1)) ⟶ M) :
    ((((cochainLinearDualFunctor P).obj M)⟦(1 : ℤ)⟧).d i j).hom f =
      -(P.d (0 - (j + 1)) (0 - (i + 1)) ≫ f) := by
  change (1 : ℤ).negOnePow • (P.d (0 - (j + 1)) (0 - (i + 1)) ≫ f) = _
  simp

/-- The signed term comparison commutes with the actual differentials. -/
lemma cochainLinearDualConeShiftTermIso_comm (M : ModuleCat.{u} R)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (cochainLinearDualConeShiftTermIso φ M i).hom ≫
        (CochainComplex.mappingCone ((cochainLinearDualMap φ).app M)).d i j =
      (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).d i j ≫
        (cochainLinearDualConeShiftTermIso φ M j).hom := by
  change i + 1 = j at hij
  subst j
  apply (cancel_mono (mappingConeTermProdIso ((cochainLinearDualMap φ).app M) (i + 1)).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (mappingConeTermProdIso ((cochainLinearDualMap φ).app M) (i + 1)).hom
      ((CochainComplex.mappingCone ((cochainLinearDualMap φ).app M)).d i (i + 1)
        ((cochainLinearDualConeShiftTermIso φ M i).hom f)) =
    (mappingConeTermProdIso ((cochainLinearDualMap φ).app M) (i + 1)).hom
      ((cochainLinearDualConeShiftTermIso φ M (i + 1)).hom
        (((((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).d
          i (i + 1)).hom f))
  apply Prod.ext
  · rw [mappingConeTermProdIso_d_fst, cochainLinearDualConeShiftTermIso_fst,
      cochainLinearDualConeShiftTermIso_fst, cochainLinearDual_d_apply,
      cochainLinearDualShiftOne_d_apply]
    change -(L.d (0 - (i + 1 + 1)) (0 - (i + 1)) ≫ inrX φ (0 - (i + 1)) ≫ f) =
      inrX φ (0 - (i + 1 + 1)) ≫
        (-(homotopyCofiber.d φ (0 - (i + 1 + 1)) (0 - (i + 1)) ≫ f))
    simp only [Preadditive.comp_neg, inrX_d_assoc]
  · rw [mappingConeTermProdIso_d_snd, cochainLinearDualConeShiftTermIso_fst,
      cochainLinearDualConeShiftTermIso_snd, cochainLinearDualConeShiftTermIso_snd,
      cochainLinearDual_d_apply, cochainLinearDualShiftOne_d_apply]
    change φ.f (0 - (i + 1)) ≫ inrX φ (0 - (i + 1)) ≫ f +
        K.d (0 - (i + 1)) (0 - i) ≫
          (-(inlX φ (0 - i) (0 - (i + 1)) (by change 0 - (i + 1) + 1 = 0 - i; omega) ≫ f)) =
      -(inlX φ (0 - (i + 1)) (0 - (i + 1 + 1))
        (by change 0 - (i + 1 + 1) + 1 = 0 - (i + 1); omega) ≫
        (-(homotopyCofiber.d φ (0 - (i + 1 + 1)) (0 - (i + 1)) ≫ f)))
    simp only [Preadditive.comp_neg, neg_neg]
    have h := congrArg (fun g => g ≫ f)
      (inlX_d φ (0 - (i + 1 + 1)) (0 - (i + 1)) (0 - i)
        (by change 0 - (i + 1 + 1) + 1 = 0 - (i + 1); omega)
        (by change 0 - (i + 1) + 1 = 0 - i; omega))
    simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc] at h
    rw [h]
    exact add_comm _ _

/-- The shifted dual cone is the actual cone of the contravariant dual map. -/
def cochainLinearDualConeShiftIso (M : ModuleCat.{u} R) :
    ((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧ ≅
      CochainComplex.mappingCone ((cochainLinearDualMap φ).app M) :=
  HomologicalComplex.Hom.isoOfComponents (cochainLinearDualConeShiftTermIso φ M)
    (cochainLinearDualConeShiftTermIso_comm φ M)

/-- Equivalently, dualizing a cone yields the reversed dual cone shifted by minus one. -/
def cochainLinearDualConeIso (M : ModuleCat.{u} R) :
    (cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M ≅
      (CochainComplex.mappingCone ((cochainLinearDualMap φ).app M))⟦(-1 : ℤ)⟧ :=
  ((shiftFunctorCompIsoId (CochainComplex (ModuleCat.{u} R) ℤ)
    (1 : ℤ) (-1) (by omega)).app _).symm ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso (cochainLinearDualConeShiftIso φ M)

end SerrePositivity

end CochainLinearDualConePart
