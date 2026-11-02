module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower

/-! # 任意の複体の主元 Koszul 完備化

## 概要

各段 `Cone(aⁿ : K → K)` の塔と、直積と差分の錐による holim から、任意の複体の完備化の関手 `complexCompletionFunctor` を作る。準同型同値で不変なので導来圏へ降ろし（`derivedComplexCompletionFunctor`）、標準射とその自然性を与える。

## 方針

有界性・射影性・各項の通常の完備性は要らない。

## 規約

旧 `ComplexCompletion`・`ComplexCompletionQuasiIso`・`ComplexCompletionDerived`・`ComplexCompletionNaturality`。

## 使われ方

DerivedCompletion の全体、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section ComplexCompletionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 任意の複体の第n主元Koszul剰余。環商による導来底変換とは区別する。 -/
abbrev complexPowerKoszulStage (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :=
  CochainComplex.mappingCone (smulId (a ^ n) K)

/-- 冪を一段下げる標準のKoszul遷移。 -/
def complexPowerKoszulTransition (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    complexPowerKoszulStage R a K (n + 1) ⟶ complexPowerKoszulStage R a K n :=
  homotopyCofiber.mapArrowHom (smulId (a ^ (n + 1)) K) (smulId (a ^ n) K)
    (fun j ↦ ⟨j - 1, by simp⟩)
    (Arrow.homMk (a • 𝟙 K) (𝟙 K) (by simp [smulId, smul_smul, pow_succ, mul_comm]))

/-- 遷移写像は係数複体の射に自然。 -/
@[reassoc] theorem complexPowerKoszulTransition_naturality (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℕ) :
    (scalarConeFunctor (a ^ (n + 1))).map f ≫ complexPowerKoszulTransition R a L n =
      complexPowerKoszulTransition R a K n ≫ (scalarConeFunctor (a ^ n)).map f := by
  dsimp only [scalarConeFunctor, complexPowerKoszulTransition]
  rw [← homotopyCofiber.mapArrowHom_comp, ← homotopyCofiber.mapArrowHom_comp]
  congr 1
  ext <;> simp

/-- 任意複体の主元Koszul段の可算直積を関手として構成する。 -/
def complexPowerKoszulProductFunctor (a : R) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj K := piObj (complexPowerKoszulStage R a K)
  map {K L} f := complexTowerProductMap R
    (K := complexPowerKoszulStage R a K) (L := complexPowerKoszulStage R a L)
    (fun n ↦ (scalarConeFunctor (a ^ n)).map f)
  map_id K := by
    apply Pi.hom_ext
    intro n
    simp only [complexTowerProductMap_projection, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  map_comp f g := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, complexTowerProductMap_projection,
      CategoryTheory.Functor.map_comp]
    simp only [← Category.assoc]
    rw [complexTowerProductMap_projection]

/-- 直積上の差分を、Arrow圏に値を持つ関手としてまとめる。 -/
def complexPowerKoszulDifferenceFunctor (a : R) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ Arrow (CochainComplex (ModuleCat.{u} R) ℤ) where
  obj K := Arrow.mk (complexTowerDifference R (complexPowerKoszulStage R a K)
    (complexPowerKoszulTransition R a K))
  map {K L} f := Arrow.homMk ((complexPowerKoszulProductFunctor R a).map f)
    ((complexPowerKoszulProductFunctor R a).map f)
    (complexTowerDifference_naturality R _ _ _
      (fun n ↦ (complexPowerKoszulTransition_naturality R a f n).symm))
  map_id K := by
    apply Arrow.hom_ext <;> exact (complexPowerKoszulProductFunctor R a).map_id K
  map_comp f g := by
    apply Arrow.hom_ext <;> exact (complexPowerKoszulProductFunctor R a).map_comp f g

/-- Arrow圏上の標準の写像錐関手。 -/
def cochainMappingConeFunctor :
    Arrow (CochainComplex (ModuleCat.{u} R) ℤ) ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj X := CochainComplex.mappingCone X.hom
  map f := homotopyCofiber.mapArrowHom _ _ (fun j ↦ ⟨j - 1, by simp⟩) f
  map_id X := homotopyCofiber.mapArrowHom_id X.hom (fun j ↦ ⟨j - 1, by simp⟩)
  map_comp f g := homotopyCofiber.mapArrowHom_comp _ _ _ (fun j ↦ ⟨j - 1, by simp⟩) f g

/-- 任意複体の主元Koszul完備化の具体的な複体関手。 -/
def complexCompletionFunctor (a : R) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  complexPowerKoszulDifferenceFunctor R a ⋙ cochainMappingConeFunctor R ⋙
    shiftFunctor _ (-1 : ℤ)

/-- 完備化候補の標準の実導来対象。 -/
def complexCompletionObject (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ConcreteDerivedCategory R := DerivedCategory.Q.obj ((complexCompletionFunctor R a).obj K)

/-- 各段の座標の零ホモトピーにより、一般複体の各Koszul剰余は導来完備。 -/
theorem complexPowerKoszulStage_isComplete (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    IsComplete R a (DerivedCategory.Q.obj (complexPowerKoszulStage R a K n)) :=
  isComplete_Q_of_scalar_pow_nullHomotopic R a _ n (scalarConeCoordinateNullHomotopy (a ^ n) K)

/-- 完備化候補は、実際の導来圏でa完備である。 -/
theorem complexCompletionObject_isComplete (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) : IsComplete R a (complexCompletionObject R a K) :=
  isComplete_complexTowerHomotopyLimitObject_of_stages R a
    (complexPowerKoszulStage R a K) (complexPowerKoszulTransition R a K)
    (complexPowerKoszulStage_isComplete R a K)

/-- 各段への標準包含はKoszul遷移と両立する。 -/
theorem complexPowerKoszulInclusion_compatible (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    CochainComplex.mappingCone.inr (smulId (a ^ (n + 1)) K) ≫
      complexPowerKoszulTransition R a K n =
        CochainComplex.mappingCone.inr (smulId (a ^ n) K) := by
  simp [CochainComplex.mappingCone.inr, complexPowerKoszulTransition,
    homotopyCofiber.mapArrowHom, homotopyCofiber.inr_desc]

/-- 任意複体からKoszul冪塔のホモトピー逆極限への標準射。 -/
def complexCompletionUnit (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K ⟶ (complexCompletionFunctor R a).obj K :=
  complexTowerCompatibleLift R _ _ K
    (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) K))
    (complexPowerKoszulInclusion_compatible R a K)

/-- 標準射を実導来圏へ移す。 -/
def complexCompletionUnitObject (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj K ⟶ complexCompletionObject R a K :=
  DerivedCategory.Q.map (complexCompletionUnit R a K)

end SerrePositivity.DerivedCompletion

end ComplexCompletionPart

section ComplexCompletionQuasiIsoPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- Arrow圏の写像錐は三角形の標準の写像錐射に一致する。 -/
theorem cochainMappingConeFunctor_map_eq
    {X Y : Arrow (CochainComplex (ModuleCat.{u} R) ℤ)} (f : X ⟶ Y) :
    (cochainMappingConeFunctor R).map f =
      CochainComplex.mappingCone.map X.hom Y.hom f.left f.right f.w.symm := by
  apply HomologicalComplex.hom_ext
  intro i
  apply CochainComplex.mappingCone.ext_from X.hom (i + 1) i rfl
  · rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inl_v_desc_f]
    simp [cochainMappingConeFunctor, homotopyCofiber.mapArrowHom,
      homotopyCofiber.inlX_desc_f,
      CochainComplex.mappingCone.inl, homotopyCofiber.inrCompHomotopy_hom,
      Homotopy.trans, Homotopy.ofEq, Homotopy.compLeft]
  · rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inr_f_desc_f]
    simp [cochainMappingConeFunctor, homotopyCofiber.mapArrowHom,
      CochainComplex.mappingCone.inr,
      homotopyCofiber.inrX_desc_f]

/-- 写像錐の射は、左包含を左側の射へ移す。 -/
theorem cochainMappingConeFunctor_inl
    {X Y : Arrow (CochainComplex (ModuleCat.{u} R) ℤ)} (f : X ⟶ Y) :
    (CochainComplex.mappingCone.inl X.hom).comp
      (CochainComplex.HomComplex.Cochain.ofHom ((cochainMappingConeFunctor R).map f))
      (add_zero (-1 : ℤ)) =
    (CochainComplex.HomComplex.Cochain.ofHom f.left).comp
      (CochainComplex.mappingCone.inl Y.hom) (zero_add (-1 : ℤ)) := by
  rw [cochainMappingConeFunctor_map_eq]
  simp [CochainComplex.mappingCone.map]

/-- 写像錐関手は両端の準同型同値を保つ。 -/
theorem cochainMappingConeFunctor_map_quasiIso
    {X Y : Arrow (CochainComplex (ModuleCat.{u} R) ℤ)} (f : X ⟶ Y)
    [QuasiIso f.left] [QuasiIso f.right] :
    QuasiIso ((cochainMappingConeFunctor R).map f) := by
  rw [cochainMappingConeFunctor_map_eq]
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
  exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
    (DerivedCategory.Q.mapTriangle.map
      (CochainComplex.mappingCone.triangleMap X.hom Y.hom f.left f.right f.w.symm))
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (by change IsIso (DerivedCategory.Q.map f.left); infer_instance)
    (by change IsIso (DerivedCategory.Q.map f.right); infer_instance)

/-- 直積のホモロジー比較は各成分の射に自然。 -/
theorem complexTowerProductMap_homology
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ} (g : ∀ n, K n ⟶ L n)
    (i : ℤ) (x : (piObj K).homology i) (n : ℕ) :
    complexProductHomologyEquiv R L i (homologyMap (complexTowerProductMap R g) i x) n =
      homologyMap (g n) i (complexProductHomologyEquiv R K i x n) := by
  have h := congrArg (fun f ↦ homologyMap f i)
    (complexTowerProductMap_projection R g n)
  simp only [homologyMap_comp] at h
  exact congrArg (fun f ↦ f.hom x) h

/-- 加群複体の可算直積は各成分の準同型同値を保つ。 -/
theorem complexTowerProductMap_quasiIso
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ} (g : ∀ n, K n ⟶ L n)
    (hg : ∀ n, QuasiIso (g n)) : QuasiIso (complexTowerProductMap R g) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro x y hxy
    apply (complexProductHomologyEquiv R K i).injective
    funext n
    have := hg n
    apply (ConcreteCategory.bijective_of_isIso (homologyMap (g n) i)).1
    simpa only [← complexTowerProductMap_homology] using
      congrArg (fun z ↦ complexProductHomologyEquiv R L i z n) hxy
  · intro y
    have hsurj : ∀ n, Function.Surjective (homologyMap (g n) i) := by
      intro n
      have := hg n
      exact (ConcreteCategory.bijective_of_isIso (homologyMap (g n) i)).2
    choose x hx using fun n ↦ hsurj n (complexProductHomologyEquiv R L i y n)
    refine ⟨(complexProductHomologyEquiv R K i).symm x, ?_⟩
    apply (complexProductHomologyEquiv R L i).injective
    funext n
    rw [complexTowerProductMap_homology, LinearEquiv.apply_symm_apply, hx]

/-- 任意のスカラー錐は係数複体の準同型同値を保つ。 -/
theorem scalarConeFunctor_map_quasiIso (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((scalarConeFunctor a).map f) := by
  let g : Arrow.mk (smulId a K) ⟶ Arrow.mk (smulId a L) :=
    Arrow.homMk f f (by simp [smulId])
  have : QuasiIso g.left := ‹QuasiIso f›
  have : QuasiIso g.right := ‹QuasiIso f›
  exact cochainMappingConeFunctor_map_quasiIso R g

/-- 任意複体の主元Koszul完備化候補は準同型同値を保つ。 -/
theorem complexCompletionFunctor_map_quasiIso (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((complexCompletionFunctor R a).map f) := by
  change QuasiIso
    (((cochainMappingConeFunctor R).map
      ((complexPowerKoszulDifferenceFunctor R a).map f))⟦(-1 : ℤ)⟧')
  apply (CochainComplex.quasiIso_shift_iff _ _).mpr
  have h : QuasiIso ((complexPowerKoszulProductFunctor R a).map f) :=
    complexTowerProductMap_quasiIso R _ (fun n ↦ scalarConeFunctor_map_quasiIso R (a ^ n) f)
  have : QuasiIso (((complexPowerKoszulDifferenceFunctor R a).map f).left) := by
    change QuasiIso ((complexPowerKoszulProductFunctor R a).map f)
    exact h
  have : QuasiIso (((complexPowerKoszulDifferenceFunctor R a).map f).right) := by
    change QuasiIso ((complexPowerKoszulProductFunctor R a).map f)
    exact h
  exact cochainMappingConeFunctor_map_quasiIso R
    ((complexPowerKoszulDifferenceFunctor R a).map f)

end SerrePositivity.DerivedCompletion

end ComplexCompletionQuasiIsoPart

section ComplexCompletionDerivedPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 完備化候補の実導来像は準同型同値を反転する。 -/
theorem complexCompletionFunctor_inverts_quasiIso (a : R) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (complexCompletionFunctor R a ⋙ DerivedCategory.Q) := by
  intro K L f hf
  have : QuasiIso f := hf
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mpr
    (complexCompletionFunctor_map_quasiIso R a f)

/-- 主元Koszul冪塔のholimによる候補を実導来圏の関手として構成する。 -/
def derivedComplexCompletionFunctor (a : R) :
    ConcreteDerivedCategory R ⥤ ConcreteDerivedCategory R :=
  Localization.lift (complexCompletionFunctor R a ⋙ DerivedCategory.Q)
    (complexCompletionFunctor_inverts_quasiIso R a) DerivedCategory.Q

/-- 導来圏の関手は、複体の具体的なholimモデルと自然に一致する。 -/
def derivedComplexCompletionComparison (a : R) :
    DerivedCategory.Q ⋙ derivedComplexCompletionFunctor R a ≅
      complexCompletionFunctor R a ⋙ DerivedCategory.Q :=
  Localization.fac (complexCompletionFunctor R a ⋙ DerivedCategory.Q)
    (complexCompletionFunctor_inverts_quasiIso R a) DerivedCategory.Q

/-- 代表複体の比較は元の複体の射と両立する。 -/
@[reassoc] theorem derivedComplexCompletionComparison_naturality (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    (derivedComplexCompletionFunctor R a).map (DerivedCategory.Q.map f) ≫
      (derivedComplexCompletionComparison R a).hom.app L =
    (derivedComplexCompletionComparison R a).hom.app K ≫
      DerivedCategory.Q.map ((complexCompletionFunctor R a).map f) :=
  (derivedComplexCompletionComparison R a).hom.naturality f

/-- 実導来圏の任意対象の完備化候補は導来完備である。 -/
theorem derivedComplexCompletionFunctor_isComplete (a : R) (X : ConcreteDerivedCategory R) :
    IsComplete R a ((derivedComplexCompletionFunctor R a).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : complexCompletionObject R a K ≅ (derivedComplexCompletionFunctor R a).obj X :=
    (derivedComplexCompletionComparison R a).symm.app K ≪≫
      (derivedComplexCompletionFunctor R a).mapIso (DerivedCategory.Q.objObjPreimageIso X)
  exact isComplete_of_iso R a e (complexCompletionObject_isComplete R a K)

end SerrePositivity.DerivedCompletion

end ComplexCompletionDerivedPart

section ComplexCompletionNaturalityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 全Koszul段への包含の族は係数複体の射と可換する。 -/
theorem complexPowerKoszulProductInclusion_naturality (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    f ≫ Pi.lift (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) L)) =
      Pi.lift (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) K)) ≫
        (complexPowerKoszulProductFunctor R a).map f := by
  apply Pi.hom_ext
  intro n
  change (f ≫ Pi.lift (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) L))) ≫
      Pi.π (complexPowerKoszulStage R a L) n =
    (Pi.lift (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) K)) ≫
      complexTowerProductMap R
        (K := complexPowerKoszulStage R a K) (L := complexPowerKoszulStage R a L)
        (fun n ↦ (scalarConeFunctor (a ^ n)).map f)) ≫
        Pi.π (complexPowerKoszulStage R a L) n
  erw [Category.assoc, Pi.lift_comp_π, Category.assoc,
    complexTowerProductMap_projection, ← Category.assoc, Pi.lift_comp_π]
  simp [scalarConeFunctor, CochainComplex.mappingCone.inr,
    homotopyCofiber.mapArrowHom, homotopyCofiber.inr_desc]

/-- 複体から完備化候補への標準射は自然である。 -/
@[reassoc] theorem complexCompletionUnit_naturality (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    f ≫ complexCompletionUnit R a L =
      complexCompletionUnit R a K ≫ (complexCompletionFunctor R a).map f := by
  change f ≫ complexCompletionUnit R a L = complexCompletionUnit R a K ≫
    (((cochainMappingConeFunctor R).map
      ((complexPowerKoszulDifferenceFunctor R a).map f))⟦(-1 : ℤ)⟧')
  apply (Cocycle.equivHomShift (K := K)
    (L := CochainComplex.mappingCone
      (complexTowerDifference R (complexPowerKoszulStage R a L)
        (complexPowerKoszulTransition R a L))) (n := (-1 : ℤ))).injective
  rw [Cocycle.equivHomShift_comp (n := (-1 : ℤ)),
    Cocycle.equivHomShift_comp_shift (n := (-1 : ℤ))]
  apply Subtype.ext
  simp only [complexCompletionUnit, complexTowerCompatibleLift,
    complexTowerHomotopyLimitLift, Cocycle.precomp, Cocycle.postcomp,
    Cocycle.mk_coe]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp only [CochainComplex.mappingCone.liftCocycle_coe, Cocycle.ofHom_coe,
    CochainComplex.mappingCone.liftCochain, Cochain.zero_comp, add_zero]
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [cochainMappingConeFunctor_inl]
  simp only [← Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  exact congrArg (fun g ↦ (Cochain.ofHom g).comp _ _)
    (complexPowerKoszulProductInclusion_naturality R a f)

/-- 標準射の実導来像。始域はまだ複体の圏である。 -/
def complexCompletionUnitDerivedInput (a : R) :
    DerivedCategory.Q ⟶ complexCompletionFunctor R a ⋙ DerivedCategory.Q where
  app K := complexCompletionUnitObject R a K
  naturality {K L} f := by
    change DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (complexCompletionUnit R a L) =
      DerivedCategory.Q.map (complexCompletionUnit R a K) ≫
        DerivedCategory.Q.map ((complexCompletionFunctor R a).map f)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      complexCompletionUnit_naturality]

/-- 実導来圏上の主元Koszul完備化候補への標準自然変換。 -/
def derivedComplexCompletionUnit (a : R) :
    𝟭 (ConcreteDerivedCategory R) ⟶ derivedComplexCompletionFunctor R a := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      DerivedCategory.Q (𝟭 (ConcreteDerivedCategory R)) := ⟨Functor.rightUnitor _⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (complexCompletionFunctor R a ⋙ DerivedCategory.Q) (derivedComplexCompletionFunctor R a) :=
    ⟨derivedComplexCompletionComparison R a⟩
  exact Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _ _ _ _
    (complexCompletionUnitDerivedInput R a)

/-- 導来圏の標準射と、複体の具体的標準射の比較図式。 -/
@[reassoc] theorem derivedComplexCompletionUnit_comparison (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedComplexCompletionUnit R a).app (DerivedCategory.Q.obj K) ≫
      (derivedComplexCompletionComparison R a).hom.app K =
        complexCompletionUnitObject R a K := by
  simp [derivedComplexCompletionUnit, Localization.liftNatTrans_app,
    Localization.Lifting.iso, complexCompletionUnitDerivedInput]

end SerrePositivity.DerivedCompletion

end ComplexCompletionNaturalityPart
