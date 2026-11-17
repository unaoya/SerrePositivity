module

public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechFunctor
public import SerrePositivity.HomologicalAlgebra.Cech.Double
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleConstantTotal
public import SerrePositivity.AlgebraicGeometry.CechIntegerTotalToColumnZeroQuasiIso
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalMonoQuasiIso
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalFunctor
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechConstantAugmentation
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitRingIso
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechConstantNaturality

/-!
概要：実際の二変数Čech図式の零次列と、元の構造射のタプルtotalを比較する。
方針：空タプルの定数角、射影の同型、同じ増大正方形、単射版total比較を使う。
規約：元の係数・被覆・増大を保持し、両方向の完全性を示す。
使われ方：相対fppfの軸比較（承認済み計画P20）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false
attribute [local instance] cechIntegerTotalShapeSymmetry

/-- 元の零次列の増大totalと、同じ元のgのタプルtotalの完全性を比較する。 -/
theorem pairedPerfectCech_zero_col_acyclic_iff
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj
        (SerrePositivity.Cech.col (pairedPerfectCech h g U V p hp hR) 0)) up).Acyclic ↔
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble g V p hp hR) up).Acyclic := by
  have hconst (A : ModuleCat.{u} ℤ)
      (F : CosimplicialObject (CochainComplex (ModuleCat.{u} ℤ) ℕ))
      (ε : (Functor.const SimplexCategory).obj (cechConstantComplex A) ⟶ F)
      (hsingle : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up).Acyclic) :
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up).Acyclic := by
    let j := cechSingleToConstantDouble A F ε
    have hm (a b : ℕ) : Mono ((j.f a).f b) := by
      cases a with
      | zero =>
        change Mono ((cechConstantSingleAugmentation A).f b)
        cases b with
        | zero =>
          rw [cechConstantSingleAugmentation_f_zero]
          infer_instance
        | succ b =>
          have hz := HomologicalComplex.isZero_single_obj_X up 0 A (b+1) (by omega)
          exact ⟨fun x y _ ↦ hz.eq_of_tgt x y⟩
      | succ a =>
        change Mono (𝟙 ((F.obj (SimplexCategory.mk a)).X b))
        infer_instance
    have hcol (a : ℕ) : QuasiIso (j.f a) := by
      cases a with
      | zero => exact cechConstantSingleAugmentation_quasiIso A
      | succ a =>
        change QuasiIso (𝟙 (F.obj (SimplexCategory.mk a)))
        infer_instance
    haveI hq := cechIntegerLiftTotal_quasiIso_of_mono_columns j hcol
      (fun a b ↦ (ModuleCat.mono_iff_injective _).mp (hm a b))
    exact fun n ↦ (exactAt_iff_of_quasiIsoAt (HomologicalComplex₂.total.map j up) n).mp
      (hsingle n)
  have hb (Z : Scheme.{u}) (j : Z ⟶ Spec (CommRingCat.of R)) :
      augmentedNerveBase j .star = 𝟙 _ := by
    change (AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
      (Arrow.mk j).augmentedCechNerve).map (𝟙 (op (WithInitial.star : AugmentedSimplexCategory))) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  letI : IsIso (augmentedNerveBase h .star) := by rw [hb]; infer_instance
  letI : IsIso (augmentedNerveBase g .star) := by rw [hb]; infer_instance
  let Q := pairedCechScheme h g .star .star
  let qbase := pullback.fst (augmentedNerveBase h .star) (augmentedNerveBase g .star) ≫
    augmentedNerveBase h .star
  letI : IsIso qbase := inferInstance
  let W := pairedCechOpen h g U V .star .star
  have hW (t : (Fin 0 → ι) × (Fin 0 → κ)) : W t = ⊤ := by
    change (_ ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) ⊓ (_ ⁻¹ᵁ ⊤) = ⊤
    simp only [Scheme.Hom.preimage_top, top_inf_eq]
  let hz := pairedCechPrimeCast h g p hR .star .star
  let φ := schemeScalarHom Q qbase
  letI : IsIso qbase.appTop := by change IsIso (Scheme.Γ.map qbase.op); infer_instance
  letI : IsIso (CommRingCat.ofHom φ) := by
    change IsIso ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ qbase.appTop)
    infer_instance
  letI := cechFiniteIndexOrder
    ((Fin (augmentedTupleLength (WithInitial.star : AugmentedSimplexCategory)) → ι) ×
      (Fin (augmentedTupleLength (WithInitial.star : AugmentedSimplexCategory)) → κ))
  let c0 := schemeStructurePerfectCechConstantAugmentation Q φ p hp hR hz W
  have hc0 : IsIso c0 := by
    haveI : ∀ n, IsIso (c0.f n) := by
      intro n
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      have hrestrict (O : Q.Opens) (hO : O = ⊤) :
          IsIso (Q.presheaf.map (homOfLE (show O ≤ ⊤ from le_top)).op) := by
        subst O
        change IsIso (Q.presheaf.map (𝟙 _))
        infer_instance
      have hβ (t : Fin (n+1) → (Fin 0 → ι) × (Fin 0 → κ)) :
          Function.Bijective (frobeniusDirectLimitMap p hp hR
            (hz (op (cechOpenIntersection W (cechTupleSupport t))))
            ((Q.presheaf.map (homOfLE (show cechOpenIntersection W (cechTupleSupport t) ≤ ⊤
              from le_top)).op).hom.comp φ)) := by
        let O := cechOpenIntersection W (cechTupleSupport t)
        have hO : O = ⊤ := by simp [O, cechOpenIntersection, hW]
        let d := Q.presheaf.map (homOfLE (show O ≤ ⊤ from le_top)).op
        letI : IsIso d := hrestrict O hO
        letI : IsIso (CommRingCat.ofHom (d.hom.comp φ)) := by
          change IsIso (CommRingCat.ofHom φ ≫ d)
          infer_instance
        exact (frobeniusDirectLimitRingIso p hp hR (hz (op O))
          (asIso (CommRingCat.ofHom (d.hom.comp φ)))).bijective
      let t0 : Fin (n+1) → (Fin 0 → ι) × (Fin 0 → κ) := fun _ ↦ (Fin.elim0, Fin.elim0)
      constructor
      · intro x y hxy
        apply (hβ t0).injective
        exact (schemeStructurePerfectCechConstantAugmentation_apply Q φ p hp hR hz W n x t0).symm.trans
          ((congrFun hxy t0).trans
            (schemeStructurePerfectCechConstantAugmentation_apply Q φ p hp hR hz W n y t0))
      · intro y
        obtain ⟨x, hx⟩ := (hβ t0).surjective (y t0)
        refine ⟨x, funext fun t ↦ ?_⟩
        have ht : t = t0 := by
          funext i
          apply Prod.ext
          · funext j
            exact Fin.elim0 j
          · funext j
            exact Fin.elim0 j
        subst t
        exact (schemeStructurePerfectCechConstantAugmentation_apply Q φ p hp hR hz W n x t0).trans hx
    exact HomologicalComplex.Hom.isIso_of_components c0
  let π (n : SimplexCategory) :=
    pullback.snd (augmentedNerveBase h .star) (augmentedNerveBase g (.of n))
  haveI (n : SimplexCategory) : IsIso (π n) := by dsimp only [π]; infer_instance
  let C (n : SimplexCategory) := pairedCechOpen h g U V .star (.of n)
  let D (n : SimplexCategory) := schemeCechTupleOpen g V (op n)
  let hN (n : SimplexCategory) := schemeCechNervePresheaf_primeCast g p hR (op n)
  let hQ (n : SimplexCategory) := pairedCechPrimeCast h g p hR .star (.of n)
  have hπ (n : SimplexCategory) (t : (Fin 0 → ι) × (Fin (n.len+1) → κ)) :
      C n t ≤ π n ⁻¹ᵁ D n t.2 := by
    change (_ ⊓ (π n ⁻¹ᵁ D n t.2)) ≤ _
    exact inf_le_right
  let m (n : SimplexCategory) :
      schemePerfectCechTupleComplex g V p hp (schemeCechNervePresheaf_primeCast g p hR) n ⟶
        pairedPerfectCechComplex h g U V p hp hR .star (.of n) :=
    schemeStructurePerfectCechRefinedPullbackMap (π n) p hp (hN n) (hQ n)
      (D n) (C n) Prod.snd (hπ n)
  have hm (n : SimplexCategory) : IsIso (m n) := by
    let N := (Arrow.mk g).cechNerve.obj (op n)
    let B := pairedCechScheme h g .star (.of n)
    let e := asIso (π n)
    let η (t : Fin (n.len+1) → κ) : (Fin 0 → ι) × (Fin (n.len+1) → κ) :=
      (Fin.elim0, t)
    have hη₁ : Prod.snd ∘ η = id := rfl
    have hη₂ : η ∘ Prod.snd = id := by
      funext t
      exact Prod.ext (Subsingleton.elim _ _) rfl
    have hC (t : Fin (n.len+1) → κ) : C n (η t) = π n ⁻¹ᵁ D n t := by
      change (_ ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) ⊓ _ = _
      simp only [Scheme.Hom.preimage_top, top_inf_eq]
      rfl
    have hη (t : Fin (n.len+1) → κ) : D n t ≤ e.inv ⁻¹ᵁ C n (η t) := by
      rw [hC, ← Scheme.Hom.comp_preimage]
      change D n t ≤ (e.inv ≫ e.hom) ⁻¹ᵁ D n t
      rw [e.inv_hom_id, Scheme.Hom.id_preimage]
    let r := schemeStructurePerfectCechRefinedPullbackMap e.inv p hp (hQ n) (hN n)
      (C n) (D n) η hη
    have hUW₁ (t : Fin (n.len+1) → κ) : D n t ≤ (𝟙 N) ⁻¹ᵁ D n (Prod.snd (η t)) := by
      simp only [η, Scheme.Hom.id_preimage, le_refl]
    have hUW₂ (t : (Fin 0 → ι) × (Fin (n.len+1) → κ)) :
        C n t ≤ (𝟙 B) ⁻¹ᵁ C n (η (Prod.snd t)) := by
      have ht : η (Prod.snd t) = t := congrFun hη₂ t
      rw [ht, Scheme.Hom.id_preimage]
    have h₁ : m n ≫ r = 𝟙 _ := by
      exact (schemeStructurePerfectCechRefinedPullbackMap_compIndex
        (π n) e.inv (𝟙 N) e.inv_hom_id p hp (hN n) (hQ n) (hN n)
        (D n) (C n) (D n) Prod.snd η (hπ n) hη hUW₁).trans
          (schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq
            (𝟙 N) rfl p hp (hN n) (D n) (Prod.snd ∘ η) hη₁ hUW₁)
    have h₂ : r ≫ m n = 𝟙 _ := by
      exact (schemeStructurePerfectCechRefinedPullbackMap_compIndex
        e.inv (π n) (𝟙 B) e.hom_inv_id p hp (hQ n) (hN n) (hQ n)
        (C n) (D n) (C n) η Prod.snd hη (hπ n) hUW₂).trans
          (schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq
            (𝟙 B) rfl p hp (hQ n) (C n) (η ∘ Prod.snd) hη₂ hUW₂)
    exact ⟨⟨r, h₁, h₂⟩⟩
  have hmnat {a b : SimplexCategory} (α : a ⟶ b) :
      schemePerfectCechTupleMap g V p hp (schemeCechNervePresheaf_primeCast g p hR) α ≫ m b =
      m a ≫ pairedPerfectCechMap h g U V p hp hR (𝟙 (WithInitial.star : AugmentedSimplexCategory)) (WithInitial.incl.map α) := by
    let z := pairedCechSchemeMap h g (𝟙 (WithInitial.star : AugmentedSimplexCategory)) (WithInitial.incl.map α)
    let k := π b ≫ (Arrow.mk g).cechNerve.map α.op
    let ρ (t : Fin (b.len+1) → κ) := t ∘ α.toOrderHom
    let σ (t : (Fin 0 → ι) × (Fin (b.len+1) → κ)) :=
      (t.1 ∘ augmentedTupleIndexMap (𝟙 (WithInitial.star : AugmentedSimplexCategory)),
        t.2 ∘ augmentedTupleIndexMap (WithInitial.incl.map α))
    have hz : z ≫ π a = k := by
      exact pullback.lift_snd _ _ _
    have hσ (t : (Fin 0 → ι) × (Fin (b.len+1) → κ)) : C b t ≤ z ⁻¹ᵁ C a (σ t) :=
      pairedCechOpen_map_le h g U V (𝟙 (WithInitial.star : AugmentedSimplexCategory)) (WithInitial.incl.map α) t
    have ht : Prod.snd ∘ σ = ρ ∘ Prod.snd := by funext t; rfl
    have hcomb (t : (Fin 0 → ι) × (Fin (b.len+1) → κ)) :
        C b t ≤ k ⁻¹ᵁ D a (ρ t.2) := by
      change C b t ≤ (π b ≫ (Arrow.mk g).cechNerve.map α.op) ⁻¹ᵁ D a (ρ t.2)
      rw [Scheme.Hom.comp_preimage]
      exact (hπ b t).trans ((π b).preimage_mono
        (schemeCechTupleOpen_map_le g V α.op t.2))
    have hcomb' (t : (Fin 0 → ι) × (Fin (b.len+1) → κ)) :
        C b t ≤ k ⁻¹ᵁ D a (Prod.snd (σ t)) := by
      change C b t ≤ k ⁻¹ᵁ D a (ρ t.2)
      exact hcomb t
    have hleft := schemeStructurePerfectCechRefinedPullbackMap_compIndex
      ((Arrow.mk g).cechNerve.map α.op) (π b) k rfl p hp (hN a) (hN b) (hQ b)
      (D a) (D b) (C b) ρ Prod.snd (schemeCechTupleOpen_map_le g V α.op) (hπ b) hcomb
    have hright := schemeStructurePerfectCechRefinedPullbackMap_compIndex
      (π a) z k hz p hp (hN a) (hQ a) (hQ b)
      (D a) (C a) (C b) Prod.snd σ (hπ a) hσ hcomb'
    exact hleft.trans hright.symm
  let A := ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)
  let Fg := schemePerfectCechTupleFunctor g V p hp (schemeCechNervePresheaf_primeCast g p hR)
  let ε := schemePerfectCechTupleConstantAugmentationHom g V p hp hR
  let Ec := cechConstantAugmentedObject A Fg ε
  let E := SerrePositivity.Cech.col (pairedPerfectCech h g U V p hp hR) 0
  let rm : Ec.right ⟶ E.right :=
    { app := m
      naturality := fun {a b} α ↦ by
        change schemePerfectCechTupleMap g V p hp
          (schemeCechNervePresheaf_primeCast g p hR) α ≫ m b =
            m a ≫ pairedPerfectCechMap h g U V p hp hR (𝟙 (WithInitial.star : AugmentedSimplexCategory)) (WithInitial.incl.map α)
        exact hmnat α }
  have hscalar (B C : Scheme.{u}) (v : B ⟶ C) (b : C ⟶ Spec (CommRingCat.of R)) :
      schemeScalarHom B (v ≫ b) = v.appTop.hom.comp (schemeScalarHom C b) := by rfl
  let w : Ec ⟶ E :=
    { left := c0
      right := rm
      w := by
        apply NatTrans.ext
        funext n
        change c0 ≫ pairedPerfectCechMap h g U V p hp hR
          (𝟙 (WithInitial.star : AugmentedSimplexCategory)) (WithInitial.starInitial.to (.of n)) =
            schemePerfectCechTupleConstantAugmentation g V p hp hR n ≫ m n
        let δ : (WithInitial.star : AugmentedSimplexCategory) ⟶ .of n := WithInitial.starInitial.to _
        let z := pairedCechSchemeMap h g (𝟙 (WithInitial.star : AugmentedSimplexCategory)) δ
        let r := π n ≫ augmentedNerveBase g (.of n)
        let ψ := schemeScalarHom (pairedCechScheme h g .star (.of n)) r
        have hzbase : z ≫ qbase = r := by
          dsimp only [z, qbase, r, π, pairedCechSchemeMap, pullback.map]
          simp only [Category.assoc, pullback.lift_fst_assoc, CategoryTheory.Functor.map_id, Category.id_comp]
          exact pullback.condition
        have hψ₀ : ψ = z.appTop.hom.comp φ := by
          change schemeScalarHom _ r = z.appTop.hom.comp (schemeScalarHom Q qbase)
          rw [← hzbase]
          exact hscalar _ _ z qbase
        have hψ₁ : ψ = (π n).appTop.hom.comp
            (schemeScalarHom ((Arrow.mk g).cechNerve.obj (op n))
              ((Arrow.mk g).augmentedCechNerve.hom.app (op n))) := by
          exact hscalar _ _ (π n) (augmentedNerveBase g (.of n))
        letI := cechFiniteIndexOrder
          ((Fin (augmentedTupleLength (WithInitial.star : AugmentedSimplexCategory)) → ι) ×
            (Fin (augmentedTupleLength (WithInitial.of n)) → κ))
        letI := cechFiniteIndexOrder (Fin (n.len+1) → κ)
        have h₀ := schemeStructurePerfectCechConstantAugmentation_naturality
          z φ ψ hψ₀ p hp hR hz (hQ n) W (C n)
          (fun t ↦ (t.1 ∘ augmentedTupleIndexMap (𝟙 (WithInitial.star : AugmentedSimplexCategory)),
            t.2 ∘ augmentedTupleIndexMap δ))
          (pairedCechOpen_map_le h g U V (𝟙 (WithInitial.star : AugmentedSimplexCategory)) δ)
        have h₁ := schemeStructurePerfectCechConstantAugmentation_naturality
          (π n) (schemeScalarHom ((Arrow.mk g).cechNerve.obj (op n))
            ((Arrow.mk g).augmentedCechNerve.hom.app (op n))) ψ hψ₁
          p hp hR (hN n) (hQ n) (D n) (C n) Prod.snd (hπ n)
        exact h₀.trans h₁.symm }
  haveI : IsIso c0 := hc0
  haveI : ∀ n, IsIso (rm.app n) := hm
  haveI : IsIso rm := NatIso.isIso_of_isIso_app _
  let eAug : Ec ≅ E := Comma.isoMk (asIso c0) (asIso rm) w.w
  let eTotal := cechIntegerLiftTotalFunctor.mapIso
    (SerrePositivity.Cech.augmentedCochain.mapIso eAug)
  let eSingle := cechIntegerLiftTotalFunctor.mapIso
    (SerrePositivity.Cech.augmentedCochain.mapIso
      (schemePerfectCechTupleSingleAugmentedIso g V p hp hR))
  constructor
  · intro h
    have hc : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (SerrePositivity.Cech.augmentedCochain.obj Ec) up).Acyclic :=
      fun n ↦ (h n).of_iso eTotal.symm
    exact schemePerfectCechTupleDouble_acyclic_of_constant g V p hp hR hc
  · intro h
    have hs : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A Fg ε)) up).Acyclic :=
      fun n ↦ (h n).of_iso eSingle.symm
    have hc := hconst A Fg ε hs
    exact fun n ↦ (hc n).of_iso eTotal


end SerrePositivity.AlgebraicGeometry
