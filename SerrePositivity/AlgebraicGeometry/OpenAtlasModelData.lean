module

public import SerrePositivity.AlgebraicGeometry.CoefficientSubalgebraFactor
public import SerrePositivity.AlgebraicGeometry.CartesianCompositeStageLimit
public import SerrePositivity.AlgebraicGeometry.FiniteAtlasOpenModels
public import SerrePositivity.AlgebraicGeometry.FiniteAffineAtlasCoefficientModel

/-!
概要：全 affine チャートと二重交叉の開の実際の模型を、一つの有限生成係数環上で取る。
方針：既に選んだ共通 affine 模型を具体的な係数図式へ移し、全ての開を一つの段へ降ろす。
規約：遷移・逆・cocycle の降下は次工程。模型の証人を実際に構成する。
使われ方：G2 の一般の有限表示対象の gluing datum の有限段への供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 全 affine チャートと二重交叉の開の、共通係数環上の具体的な模型の証人。 -/
structure OpenAtlasModelData (k : Type v) [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
    {I : Type u} {X : Scheme.{u}} (U : I → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (f : X ⟶ Spec (CommRingCat.of R)) where
  A : Subalgebra k R
  fg : A.FG
  obj : I → Scheme.{u}
  map : ∀ i, obj i ⟶ Spec (CommRingCat.of A)
  affine : ∀ i, IsAffine (obj i)
  fp : ∀ i, LocallyOfFinitePresentation (map i)
  qc : ∀ i, QuasiCompact (map i)
  qs : ∀ i, QuasiSeparated (map i)
  comparison : ∀ i, U i ⟶ obj i
  cartesian : ∀ i, IsPullback (comparison i) (j i ≫ f) (map i)
    (Spec.map (CommRingCat.ofHom (algebraMap A R)))
  overlap : ∀ i a, (obj i).Opens
  overlap_eq : ∀ i a, comparison i ⁻¹ᵁ overlap i a = j i ⁻¹ᵁ (j a).opensRange

/-- 選んだ共通 affine 模型から、一つの有限段上の全チャートと二重交叉の開の模型を実際に取る。 -/
theorem exists_openAtlasModel_of_common_affine_models
    (k : Type v) (R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {I : Type u} [Finite I] {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U : I → Scheme.{u}) [∀ i, IsAffine (U i)] (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (f : X ⟶ Spec (CommRingCat.of R))
    (A₀ : Subalgebra k R) (hA₀ : A₀.FG)
    (Y : I → Scheme.{u}) [∀ i, IsAffine (Y i)]
    (p : ∀ i, Y i ⟶ Spec (CommRingCat.of A₀)) [∀ i, LocallyOfFinitePresentation (p i)]
    (a : ∀ i, U i ⟶ Y i)
    (hpb : ∀ i, IsPullback (a i) (j i ≫ f) (p i)
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ R)))) :
    Nonempty (OpenAtlasModelData k U j f) := by
  classical
  let D := coefficientSpecDiagram k R
  let c := coefficientSpecCone k R
  have hc : IsLimit c := coefficientSpecConeIsLimit k R
  obtain ⟨s, γ, hγ⟩ := exists_coefficient_spec_factor_of_fg k R A₀ hA₀
  let i := Opposite.op s
  let g := Spec.map (CommRingCat.ofHom (algebraMap A₀ R))
  let E (b : I) := compositeStageBaseChangeDiagram D i γ (p b)
  let e (b : I) := cartesianCompositeStageCone D c i γ (p b) g hγ (a b) (j b ≫ f) (hpb b)
  have he (b : I) : IsLimit (e b) :=
    isLimit_cartesianCompositeStageCone D c i γ (p b) g hγ (a b) (j b ≫ f) (hpb b) hc
  haveI (b : (Finset R)ᵒᵖ) : IsAffine (D.obj b) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI (b : (Finset R)ᵒᵖ) : CompactSpace (D.obj b) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI (b : (Finset R)ᵒᵖ) : QuasiSeparatedSpace (D.obj b) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI {b d : (Finset R)ᵒᵖ} (q : b ⟶ d) : IsAffineHom (D.map q) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI (b : I) : QuasiCompact (p b) := inferInstance
  haveI (b : I) : QuasiSeparated (p b) := inferInstance
  haveI (b : I) (d : Over i) : CompactSpace ((E b).obj d) := by dsimp [E]; infer_instance
  haveI (b : I) (d : Over i) : QuasiSeparatedSpace ((E b).obj d) := by dsimp [E]; infer_instance
  haveI (b : I) {d l : Over i} (q : d ⟶ l) : IsAffineHom ((E b).map q) := by
    dsimp [E]; infer_instance
  let O (b d : I) : (U b).Opens := j b ⁻¹ᵁ (j d).opensRange
  have hO (b d : I) : IsCompact (O b d : Set (U b)) := isCompact_atlas_overlap U j b d
  obtain ⟨l, V, hV⟩ := exists_finite_atlas_opens_model_of_isLimit E e he O hO
  let A := Algebra.adjoin k (l.left.unop : Set R)
  refine ⟨{
    A := A
    fg := Subalgebra.fg_adjoin_finset _
    obj := fun b ↦ (E b).obj l
    map := fun b ↦ pullback.fst (D.map l.hom ≫ γ) (p b)
    affine := ?_
    fp := ?_
    qc := ?_
    qs := ?_
    comparison := fun b ↦ (e b).π.app l
    cartesian := ?_
    overlap := V
    overlap_eq := fun b d ↦ (hV b d).2
  }⟩
  · intro b
    change IsAffine (pullback (D.map l.hom ≫ γ) (p b))
    infer_instance
  · intro b
    change LocallyOfFinitePresentation (pullback.fst (D.map l.hom ≫ γ) (p b))
    infer_instance
  · intro b
    change QuasiCompact (pullback.fst (D.map l.hom ≫ γ) (p b))
    infer_instance
  · intro b
    change QuasiSeparated (pullback.fst (D.map l.hom ≫ γ) (p b))
    infer_instance
  · intro b
    change IsPullback ((e b).π.app l) (j b ≫ f)
      (pullback.fst (D.map l.hom ≫ γ) (p b)) (c.π.app l.left)
    exact isPullback_cartesianCompositeStageCone_π D c i γ (p b) g hγ (a b) (j b ≫ f) (hpb b) l

/-- 任意の affine 基底上の有限表示対象の、全チャートと二重交叉の開の模型を実際に取る。 -/
theorem exists_finite_openAtlasModel
    (k : Type v) (R : Type u) [CommRing k] [IsNoetherianRing k] [CommRing R] [Algebra k R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ 𝒰 : X.OpenCover.{u}, Finite 𝒰.I₀ ∧ (∀ i, IsAffine (𝒰.X i)) ∧
      Nonempty (OpenAtlasModelData k 𝒰.X 𝒰.f f) := by
  classical
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨A₀, hA₀, _, n, B, b, j, hB, hcover, hmodels⟩ :=
    exists_finite_affine_atlas_coefficient_model k (R := CommRingCat.of R) f
  letI (i : Fin n) : IsOpenImmersion (j i) := (hB i).1
  let 𝒰 : X.OpenCover.{u} := {
    I₀ := ULift.{u} (Fin n)
    X := fun i ↦ Spec (B i.down)
    f := fun i ↦ j i.down
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, inferInstance⟩
      intro x
      obtain ⟨i, z, hz⟩ := hcover x
      exact ⟨⟨i⟩, z, hz⟩
  }
  haveI (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec (B i.down)))
  choose C hC hAlg hFP a hCart using hmodels
  letI (i : Fin n) : CommRing (C i) := hC i
  letI (i : Fin n) : Algebra A₀ (C i) := hAlg i
  letI (i : Fin n) : Algebra.FinitePresentation A₀ (C i) := hFP i
  let Y (i : 𝒰.I₀) : Scheme.{u} := Spec (CommRingCat.of (C i.down))
  let p (i : 𝒰.I₀) : Y i ⟶ Spec (CommRingCat.of A₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap A₀ (C i.down)))
  haveI (i : 𝒰.I₀) : IsAffine (Y i) := inferInstanceAs (IsAffine (Spec _))
  haveI (i : 𝒰.I₀) : LocallyOfFinitePresentation (p i) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr (hFP i.down))
  have hCart' (i : 𝒰.I₀) : IsPullback (a i.down) (𝒰.f i ≫ f) (p i)
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ R))) := by
    change IsPullback (a i.down) (j i.down ≫ f) (p i) _
    rw [(hB i.down).2.2]
    exact hCart i.down
  refine ⟨𝒰, inferInstance, fun i ↦ inferInstance, ?_⟩
  exact exists_openAtlasModel_of_common_affine_models k R 𝒰.X 𝒰.f f A₀ hA₀ Y p (fun i ↦ a i.down) hCart'

end SerrePositivity.AlgebraicGeometry
