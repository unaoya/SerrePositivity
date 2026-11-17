module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitRingIsoNaturality
public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechZeroRow
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalBaseChange
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalTargetIso
public import SerrePositivity.AlgebraicGeometry.NilBaseChangePerfectCech
public import SerrePositivity.AlgebraicGeometry.CechAugmentedDoubleRows
public import SerrePositivity.AlgebraicGeometry.AffineScalarPerfectTupleTotal
public import SerrePositivity.AlgebraicGeometry.AffineGammaPerfectAugmentedCoefficients
public import SerrePositivity.AlgebraicGeometry.CechNerveCartesianBaseChange
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerSucc
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerUnit
public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleAffine
public import SerrePositivity.AlgebraicGeometry.RectangularCechTupleIntersection
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：同じ基底の各アフィン交叉の普遍降下性を、元の二変数Čechの行へ戻す。
方針：元のnerveの被覆の交叉ごとにアフィンのΓの増大複体を比較し、同じ行へ戻す。
規約：元の基底・被覆・Frobenius係数を保持し、局所の比較を同じ行へ戻す。
使われ方：アフィン細分と相対fppfの軸比較（承認済み計画F06）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false

private def pairedRowPointwiseProduct {Q : Type}
    (D : Q → AugmentedSimplexCategory ⥤ ModuleCat.{u} ℤ) :
    AugmentedSimplexCategory ⥤ ModuleCat.{u} ℤ :=
    { obj := fun d ↦ ModuleCat.of ℤ (∀ q : Q, (D q).obj d)
      map := fun {d e} α ↦ ModuleCat.ofHom (AddMonoidHom.pi fun q ↦
        ((D q).map α).hom.toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun q ↦ (D q).obj d) q)).toIntLinearMap
      map_id := fun d ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext q
        exact congrArg (fun z ↦ z.hom (x q)) ((D q).map_id d)
      map_comp := fun {d e f} α β ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext q
        exact congrArg (fun z ↦ z.hom (x q)) ((D q).map_comp α β) }


-- F06 の証明分割：既存の点ごとの積の完全性を同じ射影で確認する。
private theorem pairedRowPointwiseProduct_acyclic {Q : Type}
    (D : Q → AugmentedSimplexCategory ⥤ ModuleCat.{u} ℤ)
    (hD : ∀ q, (SerrePositivity.Cech.augmentedCochain.obj
      (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj (D q))).Acyclic) :
    (SerrePositivity.Cech.augmentedCochain.obj
      (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
        (pairedRowPointwiseProduct D))).Acyclic := by
  classical
  let Cq (q : Q) := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj (D q)
  let L := pairedRowPointwiseProduct D
  let C := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj L
  let K := SerrePositivity.Cech.augmentedCochain.obj C
  let Kq (q : Q) := SerrePositivity.Cech.augmentedCochain.obj (Cq q)
  let pr (q : Q) : L ⟶ D q :=
    { app := fun d ↦ ModuleCat.ofHom
        { toFun := fun x ↦ x q
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r x
            exact (int_smul_eq_zsmul ((D q).obj d).isModule r (x q)).symm }
      naturality := fun {d e} α ↦ rfl }
  let kp (q : Q) : K ⟶ Kq q := SerrePositivity.Cech.augmentedCochain.map
    (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.map (pr q))
  have hd0 (q : Q) (x : K.X 0) :
      ((K.d 0 1).hom x) q = ((Kq q).d 0 1).hom (x q) := by
    exact congrArg (fun z ↦ z.hom x) ((kp q).comm 0 1).symm
  have hds (q : Q) (i : ℕ) (x : K.X (i+1)) :
      ((K.d (i+1) (i+2)).hom x) q = ((Kq q).d (i+1) (i+2)).hom (x q) := by
    exact congrArg (fun z ↦ z.hom x) ((kp q).comm (i+1) (i+2)).symm
  have hex (q : Q) (i : ℕ) :
      Function.Exact ((Kq q).d i (i+1)).hom ((Kq q).d (i+1) (i+2)).hom := by
    have hz := hD q (i+1)
    change (Kq q).ExactAt (i+1) at hz
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (((Kq q).exactAt_iff' i (i+1) (i+2) (CochainComplex.prev_nat_succ i) (CochainComplex.next ℕ (i+1))).mp hz)
  have hpi {A B C : Q → Type u} [∀ q, Zero (C q)]
      (f : (∀ q, A q) → (∀ q, B q)) (g : (∀ q, B q) → (∀ q, C q))
      (fq : ∀ q, A q → B q) (gq : ∀ q, B q → C q)
      (hf : ∀ x q, f x q = fq q (x q)) (hg : ∀ x q, g x q = gq q (x q))
      (he : ∀ q, Function.Exact (fq q) (gq q)) : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      have hy (q : Q) : ∃ y, fq q y = x q := (he q (x q)).mp (by
        rw [← hg]
        exact congrFun hx q)
      choose y hy using hy
      exact ⟨y, funext fun q ↦ (hf y q).trans (hy q)⟩
    · rintro ⟨y, hy⟩
      funext q
      rw [hg]
      apply (he q (x q)).mpr
      exact ⟨y q, (hf y q).symm.trans (congrFun hy q)⟩
  intro i
  cases i with
  | zero =>
    rw [K.exactAt_iff' 0 0 1 CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0),
      ShortComplex.exact_iff_mono _ (K.shape 0 0 (by decide)), ModuleCat.mono_iff_injective]
    intro x y he
    funext q
    have hi := hD q 0
    change (Kq q).ExactAt 0 at hi
    rw [(Kq q).exactAt_iff' 0 0 1 CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0),
      ShortComplex.exact_iff_mono _ ((Kq q).shape 0 0 (by decide)),
      ModuleCat.mono_iff_injective] at hi
    apply hi
    change ((Kq q).d 0 1).hom (x q) = ((Kq q).d 0 1).hom (y q)
    change (K.d 0 1).hom x = (K.d 0 1).hom y at he
    exact (hd0 q x).symm.trans ((congrFun he q).trans (hd0 q y))
  | succ i =>
    rw [K.exactAt_iff' i (i+1) (i+2) (CochainComplex.prev_nat_succ i) (CochainComplex.next ℕ (i+1)),
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    cases i with
    | zero => exact hpi _ _ _ _ (fun x q ↦ hd0 q x) (fun x q ↦ hds q 0 x) (fun q ↦ hex q 0)
    | succ i =>
      exact hpi _ _ _ _ (fun x q ↦ hds q i x)
        (fun x q ↦ hds q (i+1) x) (fun q ↦ hex q (i+1))


-- F06 の証明分割：同じアフィン射の既存の Γ–Spec 比較を代入する。
private theorem pairedRowAffineGamma_acyclic {X B : Scheme.{u}} [IsAffine X] [IsAffine B]
    [IsLocallyNoetherian B] (f : X ⟶ B) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFinitePresentation f] (p : ℕ) (hp : p.Prime) (hK : (p : Γ(B, ⊤)) = 0)
    (hf : PerfectCechUniversalDescent p hp f) :
    let hN := fun m : SimplexCategory ↦ show (p : Γ((Arrow.mk f).cechNerve.obj (op m), ⊤)) = 0 from by
      have hz := congrArg (Scheme.Γ.map ((Arrow.mk f).augmentedCechNerve.hom.app (op m)).op).hom hK
      simpa only [map_natCast, map_zero] using hz
    (SerrePositivity.Cech.augmentedCochain.obj
      (affineGammaPerfectAugmentedCoefficients f p hp hK hN)).Acyclic := by
  classical
  let K := Γ(B, ⊤)
  haveI : IsNoetherianRing K :=
    IsLocallyNoetherian.component_noetherian (X := B) ⟨⊤, isAffineOpen_top B⟩
  let f0 := f ≫ B.isoSpec.hom
  have hf0 : PerfectCechUniversalDescent p hp f0 :=
    (perfectCechUniversalDescent_targetIso p hp f B.isoSpec).mpr hf
  let U : Unit → X.Opens := fun _ ↦ ⊤
  have hU (i : Unit) : IsAffineOpen (U i) := isAffineOpen_top _
  have hcU : (⨆ i, U i) = ⊤ := by simp [U]
  let F : Arrow.mk (pullback.snd f0 (𝟙 (Spec (CommRingCat.of K)))) ⟶ Arrow.mk f0 :=
    Arrow.homMk (pullback.fst f0 (𝟙 _)) (𝟙 _) pullback.condition
  haveI : IsIso F.left := by change IsIso (pullback.fst f0 (𝟙 _)); infer_instance
  haveI : IsIso F.right := by change IsIso (𝟙 (Spec (CommRingCat.of K))); infer_instance
  have H : IsPullback F.left (pullback.snd f0 (𝟙 (Spec (CommRingCat.of K)))) f0 F.right :=
    IsPullback.of_hasPullback f0 (𝟙 _)
  have hbase : F.right = Spec.map (CommRingCat.ofHom (RingHom.id K)) := (Spec.map_id _).symm
  have hPC := (nilBaseChange_tupleTotal_acyclic_iff
    (pullback.snd f0 (𝟙 (Spec (CommRingCat.of K)))) f0 F H (RingHom.id K) hbase
      p hp hK hK U hU).mpr
        (hf0 K hK (𝟙 _) Unit (fun i ↦ F.left ⁻¹ᵁ U i)
          (fun i ↦ (hU i).preimage F.left) (F.left.iSup_preimage_eq_top hcU))
  have hx := (affineScalarPerfectCech_exact_iff_tuple_total_acyclic _ f0 p hp hK U hU hcU).mpr hPC
  have hs : schemeScalarHom _ f0 = f.appTop.hom := by
    have he : f0 = schemeScalarMorphism _ f.appTop.hom := by
      change f ≫ B.toSpecΓ = X.toSpecΓ ≫ Spec.map f.appTop
      exact Scheme.toSpecΓ_naturality f
    rw [he, schemeScalarHom_scalarMorphism]
  rw [hs] at hx
  let hN := fun m : SimplexCategory ↦ show (p : Γ((Arrow.mk f).cechNerve.obj (op m), ⊤)) = 0 from by
    have hz := congrArg (Scheme.Γ.map ((Arrow.mk f).augmentedCechNerve.hom.app (op m)).op).hom hK
    simpa only [map_natCast, map_zero] using hz
  have hy := (ringCechExact_iff_integer_acyclic _).mp hx
  let e := SerrePositivity.Cech.augmentedCochain.mapIso
    (affineGammaPerfectAugmentedCoefficientsIso f p hp hK hN)
  exact fun m ↦ (hy m).of_iso e

private theorem pairedRowAffineDiagram_acyclic {X B : Scheme.{u}} [IsAffine X] [IsAffine B]
    [IsLocallyNoetherian B] (f : X ⟶ B) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFinitePresentation f] (p : ℕ) (hp : p.Prime)
    (hDN : ∀ d : AugmentedSimplexCategory,
      (p : Γ((AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
        (Arrow.mk f).augmentedCechNerve).obj (op d), ⊤)) = 0)
    (hf : PerfectCechUniversalDescent p hp f) :
    (SerrePositivity.Cech.augmentedCochain.obj
      (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
        (frobeniusRingDiagram
          ((AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
            (Arrow.mk f).augmentedCechNerve).rightOp ⋙ Scheme.Γ) p hp hDN))).Acyclic := by
  let C := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
    (frobeniusRingDiagram
      ((AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
        (Arrow.mk f).augmentedCechNerve).rightOp ⋙ Scheme.Γ) p hp hDN)
  let hN := fun m : SimplexCategory ↦ hDN (.of m)
  let e : C ≅ affineGammaPerfectAugmentedCoefficients f p hp (hDN .star) hN :=
    Comma.isoMk (Iso.refl _) (Iso.refl _) (by
      apply NatTrans.ext
      funext m
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change (((affineGammaPerfectAugmentedCoefficients f p hp (hDN .star) hN).hom.app m).hom z) =
        frobeniusDirectLimitMap p hp (hDN .star) (hN m)
          (Scheme.Γ.map ((Arrow.mk f).augmentedCechNerve.hom.app (op m)).op).hom z
      exact affineGammaPerfectAugmentedCoefficients_hom_app_apply f p hp (hDN .star) hN m z)
  exact fun m ↦ (pairedRowAffineGamma_acyclic f p hp (hDN .star) hf m).of_iso
    (SerrePositivity.Cech.augmentedCochain.mapIso e).symm

private theorem pairedRow_finiteFiberPower_properties {Y S : Scheme.{u}}
    (g : Y ⟶ S) [IsSeparated g] [LocallyOfFinitePresentation g] (n : ℕ) :
      IsSeparated (WidePullback.base (fun _ : Fin (n+1) ↦ g)) ∧
        LocallyOfFinitePresentation (WidePullback.base (fun _ : Fin (n+1) ↦ g)) := by
  induction n with
  | zero =>
    rw [← finiteFiberPowerZeroIso_hom_base g]
    exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
    haveI := ih.1
    haveI := ih.2
    let z := WidePullback.lift (WidePullback.base (fun _ : Fin (n+2) ↦ g))
      (fun i : Fin (n+1) ↦ WidePullback.π (fun _ : Fin (n+2) ↦ g) i.succ)
      (fun i ↦ WidePullback.π_arrow (fun _ : Fin (n+2) ↦ g) i.succ)
    have H := isPullback_finiteFiberPowerSucc g n
    haveI : IsSeparated z := MorphismProperty.of_isPullback H.flip inferInstance
    haveI : LocallyOfFinitePresentation z := MorphismProperty.of_isPullback H.flip inferInstance
    have hz : z ≫ WidePullback.base (fun _ : Fin (n+1) ↦ g) =
        WidePullback.base (fun _ : Fin (n+2) ↦ g) := WidePullback.lift_base _ _ _ _
    rw [← hz]
    exact ⟨inferInstance, inferInstance⟩

-- F06 の証明分割：同じ開の係数同型と添字交換の自然性。
private def pairedRowCanonicalOpen {R : Type u} [CommRing R] {A Y : Scheme.{u}}
    (h : A ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {κ : Type} [Fintype κ] [DecidableEq κ] (V : κ → Y.Opens) (n b : ℕ)
    (q : Fin (b+1) → (Fin (n+1) → κ)) (d : AugmentedSimplexCategory) :
    (pairedCechScheme h g d (.of (SimplexCategory.mk n))).Opens :=
  cechOpenIntersection (pairedCechOpen h g (fun _ : Unit ↦ ⊤) V d (.of (SimplexCategory.mk n)))
    (cechTupleSupport (fun r : Fin (b+1) ↦ (fun _ ↦ (), q r)))

private def pairedRowActualFunctor {R : Type u} [CommRing R] {A Y : Scheme.{u}}
    (h : A ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {κ : Type} [Fintype κ] [DecidableEq κ] (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (n b : ℕ) :
    AugmentedSimplexCategory ⥤ ModuleCat.{u} ℤ :=
  ((Functor.curryObj (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR)).flip.obj
    (.of (SimplexCategory.mk n))) ⋙ HomologicalComplex.eval (ModuleCat.{u} ℤ) up b

private def pairedRowReindexIso {R : Type u} [CommRing R] {A Y : Scheme.{u}}
    (h : A ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {κ : Type} [Fintype κ] [DecidableEq κ] (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (n b : ℕ)
    (M₀ : ∀ {d e : AugmentedSimplexCategory}, (d ⟶ e) →
      (pairedCechScheme h g e (.of (SimplexCategory.mk n)) ⟶
        pairedCechScheme h g d (.of (SimplexCategory.mk n))))
    (hM₀ : ∀ {d e : AugmentedSimplexCategory} (α : d ⟶ e),
      M₀ α = pairedCechSchemeMap h g α (𝟙 (.of (SimplexCategory.mk n))))
    (AN : (Fin (b+1) → (Fin (n+1) → κ)) → AugmentedSimplexCategoryᵒᵖ ⥤ Scheme.{u})
    (hDN : ∀ q d, (p : Γ((AN q).obj (op d), ⊤)) = 0)
    (eΓ : ∀ q d, Γ((AN q).obj (op d), ⊤) ≅
      Γ(pairedCechScheme h g d (.of (SimplexCategory.mk n)), pairedRowCanonicalOpen h g V n b q d))
    (hnat : ∀ q {d e : AugmentedSimplexCategory} (α : d ⟶ e)
      (hc : pairedRowCanonicalOpen h g V n b q e ≤
        M₀ α ⁻¹ᵁ
          pairedRowCanonicalOpen h g V n b q d),
      (eΓ q d).hom ≫ Scheme.Hom.appLE
          (X := pairedCechScheme h g e (.of (SimplexCategory.mk n)))
          (Y := pairedCechScheme h g d (.of (SimplexCategory.mk n)))
          (M₀ α)
          (pairedRowCanonicalOpen h g V n b q d) (pairedRowCanonicalOpen h g V n b q e) hc =
        ((AN q).map α.op).appTop ≫ (eΓ q e).hom) :
    pairedRowPointwiseProduct (fun q ↦ frobeniusRingDiagram ((AN q).rightOp ⋙ Scheme.Γ) p hp (hDN q)) ≅
      pairedRowActualFunctor h g V p hp hR n b := by
  classical

  have hM : @M₀ = (fun (d e : AugmentedSimplexCategory) (α : d ⟶ e) ↦ pairedCechSchemeMap h g α (𝟙 (.of (SimplexCategory.mk n)))) := by
    funext d e α
    exact hM₀ α
  subst M₀

  let a : AugmentedSimplexCategory := .of (SimplexCategory.mk n)
  let Q := Fin (b+1) → (Fin (n+1) → κ)
  let P (d : AugmentedSimplexCategory) := pairedCechScheme h g d a
  let M {d e : AugmentedSimplexCategory} (α : d ⟶ e) := pairedCechSchemeMap h g α (𝟙 a)
  let D (q : Q) := frobeniusRingDiagram ((AN q).rightOp ⋙ Scheme.Γ) p hp (hDN q)
  let L := pairedRowPointwiseProduct D
  let I (d : AugmentedSimplexCategory) :=
    (Fin (augmentedTupleLength d) → Unit) × (Fin (n+1) → κ)
  let J (d : AugmentedSimplexCategory) := Fin (b+1) → I d
  let ξ (d : AugmentedSimplexCategory) : J d ≃ Q :=
    { toFun := fun t r ↦ (t r).2
      invFun := fun q r ↦ (fun _ ↦ (), q r)
      left_inv := fun t ↦ funext fun r ↦ Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ ↦ rfl }
  let U (d : AugmentedSimplexCategory) : I d → (P d).Opens :=
    pairedCechOpen h g (fun _ : Unit ↦ ⊤) V d a
  let AO (d : AugmentedSimplexCategory) (t : J d) : (P d).Opens :=
    cechOpenIntersection (U d) (cechTupleSupport t)
  let Acoef (d : AugmentedSimplexCategory) (t : J d) :=
    FrobeniusDirectLimit Γ(P d, AO d t) p hp (pairedCechPrimeCast h g p hR d a (op (AO d t)))
  let c (q : Q) (d : AugmentedSimplexCategory) :
      FrobeniusDirectLimit Γ((AN q).obj (op d), ⊤) p hp (hDN q d) ≃+* Acoef d ((ξ d).symm q) :=
    frobeniusDirectLimitRingIso p hp (hDN q d)
      (pairedCechPrimeCast h g p hR d a (op (AO d ((ξ d).symm q)))) (eΓ q d)

  have hcNat (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e)
      (hc : AO e ((ξ e).symm q) ≤ M α ⁻¹ᵁ AO d ((ξ d).symm q)) (x : (D q).obj d) :
      frobeniusDirectLimitMap p hp
          (pairedCechPrimeCast h g p hR d a (op (AO d ((ξ d).symm q))))
          (pairedCechPrimeCast h g p hR e a (op (AO e ((ξ e).symm q))))
          ((M α).appLE _ _ hc).hom (c q d x) = c q e (((D q).map α).hom x) := by
    let v := (M α).appLE (AO d ((ξ d).symm q)) (AO e ((ξ e).symm q)) hc
    have hr := hnat q α hc
    exact (frobeniusDirectLimitRingIso_naturality p hp _ _ _ _
      (eΓ q d) (eΓ q e) ((AN q).map α.op).appTop.hom v.hom hr.symm x).symm

  let R := ((Functor.curryObj (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR)).flip.obj a) ⋙
    HomologicalComplex.eval (ModuleCat.{u} ℤ) up b
  let eR (d : AugmentedSimplexCategory) :=
    (RingEquiv.piCongrRight (fun q ↦ c q d)).trans (RingEquiv.piCongrLeft' (Acoef d) (ξ d)).symm
  let em (d : AugmentedSimplexCategory) : L.obj d ≅ R.obj d :=
    ((eR d).toAddEquiv.toIntLinearEquiv
      (modM := (L.obj d).isModule) (modM₂ := (R.obj d).isModule)).toModuleIso

  have hem (d : AugmentedSimplexCategory) (x : L.obj d) (q : Q) :
      ((em d).hom.hom x) ((ξ d).symm q) = c q d (x q) := by
    change (Equiv.piCongrLeft' (Acoef d) (ξ d)).symm
      (fun q ↦ c q d (x q)) ((ξ d).symm q) = c q d (x q)
    exact Equiv.piCongrLeft'_symm_apply_apply _ _ _ _

  let eNat : L ≅ R := NatIso.ofComponents em (by
    intro d e α

    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (∀ q : Q, FrobeniusDirectLimit Γ((AN q).obj (op d), ⊤) p hp (hDN q d)) at x
    funext t
    obtain ⟨q, rfl⟩ := (ξ e).symm.surjective t

    let ρ (z : I e) : I d :=
      (z.1 ∘ augmentedTupleIndexMap α, z.2 ∘ augmentedTupleIndexMap (𝟙 a))
    have hidx : ρ ∘ (ξ e).symm q = (ξ d).symm q := by
      funext r
      apply Prod.ext
      · rfl
      · simp only [ρ, ξ, augmentedTupleIndexMap_id, Function.comp_id]
        rfl

    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]

    rw [hem]

    change c q e (((D q).map α).hom (x q)) =
      ((schemeStructurePerfectCechRefinedPullbackMap (M α) p hp
        (pairedCechPrimeCast h g p hR d a) (pairedCechPrimeCast h g p hR e a)
        (U d) (U e) ρ (pairedCechOpen_map_le h g (fun _ : Unit ↦ ⊤) V α (𝟙 a))).f b).hom
        ((em d).hom.hom x) ((ξ e).symm q)

    have hval (t : J d) (ht : t = (ξ d).symm q)
        (hc : AO e ((ξ e).symm q) ≤ M α ⁻¹ᵁ AO d t) :
        frobeniusDirectLimitMap p hp _ _ ((M α).appLE (AO d t)
          (AO e ((ξ e).symm q)) hc).hom (((em d).hom.hom x) t) =
          c q e (((D q).map α).hom (x q)) := by
      subst t
      rw [hem]
      exact hcNat q α hc (x q)
    rw [schemeStructurePerfectCechRefinedPullbackMap_apply]
    exact (hval _ hidx _).symm)

  exact eNat

private def pairedRowEvaluationIso
    (F : AugmentedSimplexCategory ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ) (b : ℕ) :
    AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
        (F ⋙ HomologicalComplex.eval (ModuleCat.{u} ℤ) up b) ≅
      (CosimplicialObject.Augmented.whiskeringObj _ _
        (HomologicalComplex.eval (ModuleCat.{u} ℤ) up b)).obj
          (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj F) :=
  Comma.isoMk (Iso.refl _) (Iso.refl _) (by
    apply NatTrans.ext
    funext m
    rfl)

/-- 同じ各正次数の底変換の普遍降下性から、同じ行の増大totalの完全性を得る。 -/
theorem pairedCech_row_acyclic_of_baseChangeDescent {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A Y : Scheme.{u}} [IsAffine A]
    (h : A ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation h] [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g]
    {κ : Type} [Fintype κ] [DecidableEq κ] (V : κ → Y.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (hcV : (⨆ j, V j) = ⊤)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hd : ∀ j : ℕ, 0 < j → PerfectCechUniversalDescent p hp
      (pullback.snd h (augmentedNerveBase g (SerrePositivity.Cech.simplex j)))) :
    ∀ j : ℕ, 0 < j →
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ) (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.row
        (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR) j)) (.up ℕ)).Acyclic := by
  classical
  have hfib := pairedRow_finiteFiberPower_properties g
  intro j hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  let a : AugmentedSimplexCategory := .of (SimplexCategory.mk n)
  let G := (AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk g).augmentedCechNerve).obj (op a)
  let δ := augmentedNerveBase g a
  haveI : IsSeparated δ := (hfib n).1
  haveI : LocallyOfFinitePresentation δ := (hfib n).2
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian δ
  haveI : G.IsSeparated := ⟨by rw [← terminal.comp_from δ]; infer_instance⟩
  let W (t : Fin (n+1) → κ) : G.Opens := schemeCechTupleOpen g V (op (SimplexCategory.mk n)) t
  have hW (t) : IsAffineOpen (W t) := schemeCechTupleOpen_isAffine g V hV n t
  let β := pullback.snd h δ
  haveI : IsAffineHom β := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback h δ) (inferInstance : IsAffineHom h)
  have hβ : PerfectCechUniversalDescent p hp β := hd (n+1) (Nat.zero_lt_succ n)
  let O (b : ℕ) (q : Fin (b+1) → (Fin (n+1) → κ)) : G.Opens :=
    cechOpenIntersection W (cechTupleSupport q)
  have hO (b) (q : Fin (b+1) → (Fin (n+1) → κ)) : IsAffineOpen (O b q) := by
    apply cechOpenIntersection_isAffineOpen W hW
    exact ⟨q 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  haveI (b) (q : Fin (b+1) → (Fin (n+1) → κ)) : IsAffine (O b q).toScheme := hO b q
  haveI (b) (q : Fin (b+1) → (Fin (n+1) → κ)) :
      IsAffineHom (pullback.snd β (O b q).ι) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback β (O b q).ι)
      (inferInstance : IsAffineHom β)
  haveI (b) (q : Fin (b+1) → (Fin (n+1) → κ)) : IsAffine (pullback β (O b q).ι) :=
    isAffine_of_isAffineHom (pullback.snd β (O b q).ι)
  apply cechIntegerAugmentedDouble_acyclic_of_rows
  intro b
  let Q := Fin (b+1) → (Fin (n+1) → κ)
  let f (q : Q) := pullback.snd β (O b q).ι

  let F (q : Q) : Arrow.mk (f q) ⟶ Arrow.mk h :=
    Arrow.homMk (pullback.fst β (O b q).ι ≫ pullback.fst h δ) ((O b q).ι ≫ δ)
      ((IsPullback.of_hasPullback β (O b q).ι).paste_horiz
        (IsPullback.of_hasPullback h δ)).w
  have HF (q : Q) : IsPullback (F q).left (f q) h (F q).right :=
    (IsPullback.of_hasPullback β (O b q).ι).paste_horiz (IsPullback.of_hasPullback h δ)
  let NF (q : Q) := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.map
    (Arrow.mapAugmentedCechNerve (F q))
  have hb {X S : Scheme.{u}} (v : X ⟶ S) : augmentedNerveBase v .star = 𝟙 _ := by
    exact CategoryTheory.Functor.map_id _ _
  have HN (q : Q) (d : AugmentedSimplexCategory) :
      IsPullback ((NF q).app (op d)) (augmentedNerveBase (f q) d)
        (augmentedNerveBase h d) (F q).right := by
    cases d with
    | star =>
      rw [hb (f q), hb h]
      change IsPullback (F q).right (𝟙 _) (𝟙 _) (F q).right
      exact IsPullback.of_id_snd
    | of d => exact isPullback_cechNerve_base (F q) (HF q) (op d)
  let P (d : AugmentedSimplexCategory) := pairedCechScheme h g d a
  let π (d : AugmentedSimplexCategory) := pullback.snd (augmentedNerveBase h d) δ
  let T (q : Q) (d : AugmentedSimplexCategory) : (P d).Opens := π d ⁻¹ᵁ O b q
  have HA (q : Q) (d : AugmentedSimplexCategory) :
      IsPullback ((T q d).ι ≫ pullback.fst (augmentedNerveBase h d) δ)
        (π d ∣_ O b q) (augmentedNerveBase h d) (F q).right :=
    (isPullback_morphismRestrict (π d) (O b q)).flip.paste_horiz
      (IsPullback.of_hasPullback (augmentedNerveBase h d) δ)
  let E (q : Q) (d : AugmentedSimplexCategory) :=
    (HN q d).isoPullback ≪≫ (HA q d).isoPullback.symm
  have efst (q : Q) (d) :
      (E q d).hom ≫ (T q d).ι ≫ pullback.fst (augmentedNerveBase h d) δ =
        (NF q).app (op d) := by
    dsimp only [E]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      (HA q d).isoPullback_inv_fst, (HN q d).isoPullback_hom_fst]
  have esnd (q : Q) (d) :
      (E q d).hom ≫ (π d ∣_ O b q) = augmentedNerveBase (f q) d := by
    dsimp only [E]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      (HA q d).isoPullback_inv_snd, (HN q d).isoPullback_hom_snd]

  let AN (q : Q) := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk (f q)).augmentedCechNerve
  let H := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk h).augmentedCechNerve
  let M {d e : AugmentedSimplexCategory} (α : d ⟶ e) := pairedCechSchemeMap h g α (𝟙 a)
  have hπ {d e : AugmentedSimplexCategory} (α : d ⟶ e) : M α ≫ π d = π e := by
    dsimp only [M, π, pairedCechSchemeMap, pullback.map]
    rw [pullback.lift_snd]
    rw [show (𝟙 a).op = 𝟙 (op a) from rfl, CategoryTheory.Functor.map_id, Category.comp_id]
  have hfst {d e : AugmentedSimplexCategory} (α : d ⟶ e) :
      M α ≫ pullback.fst (augmentedNerveBase h d) δ =
        pullback.fst (augmentedNerveBase h e) δ ≫ H.map α.op := by
    dsimp only [M, pairedCechSchemeMap, pullback.map, H]
    exact pullback.lift_fst _ _ _
  have hcover (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e) :
      T q e ≤ M α ⁻¹ᵁ T q d := by
    dsimp only [T]
    rw [← Scheme.Hom.comp_preimage, hπ]
  let s (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e) :=
    (M α).resLE (T q d) (T q e) (hcover q α)
  have hsι (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e) :
      s q α ≫ (T q d).ι = (T q e).ι ≫ M α := Scheme.Hom.resLE_comp_ι _ _
  have hsF (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e) :
      s q α ≫ ((T q d).ι ≫ pullback.fst (augmentedNerveBase h d) δ) =
        ((T q e).ι ≫ pullback.fst (augmentedNerveBase h e) δ) ≫ H.map α.op := by
    rw [← Category.assoc, hsι, Category.assoc, hfst, ← Category.assoc]
  have hsO (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e) :
      s q α ≫ (π d ∣_ O b q) = (π e ∣_ O b q) := by
    apply (cancel_mono (O b q).ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hsι,
      Category.assoc, hπ, morphismRestrict_ι]
  have hEnat (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e) :
      (AN q).map α.op ≫ (E q d).hom = (E q e).hom ≫ s q α := by
    apply (HA q d).hom_ext
    · calc
        ((AN q).map α.op ≫ (E q d).hom) ≫
            ((T q d).ι ≫ pullback.fst (augmentedNerveBase h d) δ) =
          (AN q).map α.op ≫ (NF q).app (op d) := by
            simp only [Category.assoc, efst]
        _ = (NF q).app (op e) ≫ H.map α.op := (NF q).naturality α.op
        _ = ((E q e).hom ≫ ((T q e).ι ≫ pullback.fst (augmentedNerveBase h e) δ)) ≫
            H.map α.op := by rw [efst]
        _ = ((E q e).hom ≫ s q α) ≫
            ((T q d).ι ≫ pullback.fst (augmentedNerveBase h d) δ) := by
              simp only [Category.assoc, hsF]
    · have hn : (AN q).map α.op ≫ augmentedNerveBase (f q) d =
          augmentedNerveBase (f q) e := by
        unfold augmentedNerveBase
        rw [← CategoryTheory.Functor.map_comp]
        congr 1
      rw [Category.assoc, esnd, hn, Category.assoc, hsO, esnd]
  let eΓ (q : Q) (d : AugmentedSimplexCategory) :=
    asIso (E q d).inv.appTop ≪≫ (T q d).topIso
  have hinv (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e) :
      s q α ≫ (E q d).inv = (E q e).inv ≫ (AN q).map α.op := by
    apply (cancel_mono (E q d).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      hEnat, Iso.inv_hom_id_assoc]
  have hres (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e) :
      (s q α).appTop ≫ (T q e).topIso.hom =
        (T q d).topIso.hom ≫ (M α).appLE (T q d) (T q e) (hcover q α) := by
    change ((M α).resLE (T q d) (T q e) (hcover q α)).app ⊤ ≫ _ = _
    rw [Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hΓnat (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e) :
      (eΓ q d).hom ≫ (M α).appLE (T q d) (T q e) (hcover q α) =
        ((AN q).map α.op).appTop ≫ (eΓ q e).hom := by
    dsimp only [eΓ]
    simp only [Iso.trans_hom, asIso_hom]
    calc
      (E q d).inv.appTop ≫ (T q d).topIso.hom ≫
          (M α).appLE (T q d) (T q e) (hcover q α) =
            (E q d).inv.appTop ≫ (s q α).appTop ≫ (T q e).topIso.hom := by rw [hres]
      _ = (s q α ≫ (E q d).inv).appTop ≫ (T q e).topIso.hom := by
        rw [Scheme.Hom.comp_appTop, Category.assoc]
      _ = ((E q e).inv ≫ (AN q).map α.op).appTop ≫ (T q e).topIso.hom := by rw [hinv]
      _ = ((AN q).map α.op).appTop ≫ (E q e).inv.appTop ≫ (T q e).topIso.hom := by
        rw [Scheme.Hom.comp_appTop, Category.assoc]

  let hK (q : Q) :=
    schemeScalarPresheaf_primeCast (O b q).toScheme ((O b q).ι ≫ δ) p hR (op ⊤)
  let hDN (q : Q) (d : AugmentedSimplexCategory) : (p : Γ((AN q).obj (op d), ⊤)) = 0 := by
    have hz := congrArg (augmentedNerveBase (f q) d).appTop.hom (hK q)
    simpa only [map_natCast, map_zero] using hz
  let D (q : Q) := frobeniusRingDiagram ((AN q).rightOp ⋙ Scheme.Γ) p hp (hDN q)
  let Cq (q : Q) := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj (D q)
  have hD (q : Q) : (SerrePositivity.Cech.augmentedCochain.obj (Cq q)).Acyclic :=
    pairedRowAffineDiagram_acyclic (f q) p hp (hDN q)
      (perfectCechUniversalDescent_baseChange p hp β (O b q).ι hβ)
  let L := pairedRowPointwiseProduct D
  let C := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj L
  let K := SerrePositivity.Cech.augmentedCochain.obj C
  have hKprod : K.Acyclic := pairedRowPointwiseProduct_acyclic D hD

  have htop (d : AugmentedSimplexCategory) (t : Fin (augmentedTupleLength d) → Unit) :
      augmentedTupleOpen h (fun _ : Unit ↦ ⊤) d t = ⊤ := by
    cases d <;> simp [augmentedTupleOpen, schemeCechTupleOpen]
  have hCan (q : Q) (d) : pairedRowCanonicalOpen h g V n b q d = T q d := by
    dsimp only [pairedRowCanonicalOpen, T, O]
    rw [cechOpenIntersection_tupleSupport_eq_iInf,
      cechOpenIntersection_tupleSupport_eq_iInf, schemePreimage_finite_iInf]
    apply iInf_congr
    intro r
    dsimp only [pairedCechOpen]
    rw [htop, Scheme.Hom.preimage_top, top_inf_eq]
    rfl
  let cΓ (q : Q) (d : AugmentedSimplexCategory) := eΓ q d ≪≫
    ((P d).presheaf.mapIso (eqToIso (congrArg op (hCan q d)))).symm
  have hΓeq (q : Q) {d e : AugmentedSimplexCategory} (α : d ⟶ e)
      (U₀ : (P d).Opens) (U₁ : (P e).Opens) (h₀ : U₀ = T q d) (h₁ : U₁ = T q e)
      (hc : U₁ ≤ M α ⁻¹ᵁ U₀) :
      (eΓ q d).hom ≫ (P d).presheaf.map (eqToHom (congrArg op h₀.symm)) ≫
          (M α).appLE U₀ U₁ hc =
        ((AN q).map α.op).appTop ≫ (eΓ q e).hom ≫
          (P e).presheaf.map (eqToHom (congrArg op h₁.symm)) := by
    subst U₀
    subst U₁
    simpa only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] using hΓnat q α

  let eNat := pairedRowReindexIso h g V p hp hR n b (fun {d e} α ↦ M α) (fun {d e} α ↦ rfl) AN hDN cΓ
    (fun q {d e} α hc ↦ hΓeq q α _ _ (hCan q _) (hCan q _) hc)

  let eC := SerrePositivity.Cech.augmentedCochain.mapIso
    (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.mapIso eNat)

  let eE := SerrePositivity.Cech.augmentedCochain.mapIso
    (pairedRowEvaluationIso
      ((Functor.curryObj (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR)).flip.obj a) b)
  exact fun i ↦ (hKprod i).of_iso (eC ≪≫ eE)

end SerrePositivity.AlgebraicGeometry
