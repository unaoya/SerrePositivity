module

public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechZeroAxes
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalTargetIso
public import SerrePositivity.AlgebraicGeometry.NilBaseChangePerfectCech
public import SerrePositivity.AlgebraicGeometry.CechNerveCartesianBaseChange
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerUnit
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerSucc
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：固定した正次数のアフィン基底の降下性を、元の二変数Čechの列へ送る。
方針：Γ–Spec表示とCartesianなnerveの同型を、既存の零次列の比較へ戻す。
規約：元の基底・係数・被覆と増大点を保持し、仮定を強めない。
使われ方：アフィン細分と相対fppfの軸比較（承認済み計画F05）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false

/-- 同じ各正次数の底変換の普遍降下性から、同じ列の増大totalの完全性を得る。 -/
theorem pairedCech_col_acyclic_of_baseChangeDescent {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A Y : Scheme.{u}} [IsAffine A]
    (h : A ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation h] [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g]
    {κ : Type} [Fintype κ] [DecidableEq κ] (V : κ → Y.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (hcV : (⨆ j, V j) = ⊤)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hd : ∀ i : ℕ, 0 < i → PerfectCechUniversalDescent p hp
      (pullback.snd g (augmentedNerveBase h (SerrePositivity.Cech.simplex i)))) :
    ∀ i : ℕ, 0 < i →
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ) (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.col
        (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR) i)) (.up ℕ)).Acyclic := by
  classical
  have hfib (n : ℕ) :
      IsAffineHom (WidePullback.base (fun _ : Fin (n+1) ↦ h)) ∧
        LocallyOfFinitePresentation (WidePullback.base (fun _ : Fin (n+1) ↦ h)) := by
    induction n with
    | zero =>
      rw [← finiteFiberPowerZeroIso_hom_base h]
      exact ⟨inferInstance, inferInstance⟩
    | succ n ih =>
      haveI := ih.1
      haveI := ih.2
      let z := WidePullback.lift (WidePullback.base (fun _ : Fin (n+2) ↦ h))
        (fun i : Fin (n+1) ↦ WidePullback.π (fun _ : Fin (n+2) ↦ h) i.succ)
        (fun i ↦ WidePullback.π_arrow (fun _ : Fin (n+2) ↦ h) i.succ)
      have H := isPullback_finiteFiberPowerSucc h n
      haveI : IsAffineHom z := MorphismProperty.of_isPullback H.flip inferInstance
      haveI : LocallyOfFinitePresentation z := MorphismProperty.of_isPullback H.flip inferInstance
      have hz : z ≫ WidePullback.base (fun _ : Fin (n+1) ↦ h) =
          WidePullback.base (fun _ : Fin (n+2) ↦ h) := WidePullback.lift_base _ _ _ _
      rw [← hz]
      exact ⟨inferInstance, inferInstance⟩
  intro i hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  let a : AugmentedSimplexCategory := .of (SimplexCategory.mk n)
  let N := (AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk h).augmentedCechNerve).obj (op a)
  let δ := augmentedNerveBase h a
  haveI : IsAffineHom δ := (hfib n).1
  haveI : LocallyOfFinitePresentation δ := (hfib n).2
  haveI : IsAffine N := isAffine_of_isAffineHom δ
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian δ
  let K := Γ(N, ⊤)
  haveI : IsNoetherianRing K :=
    IsLocallyNoetherian.component_noetherian (X := N) ⟨⊤, isAffineOpen_top N⟩
  let hK : (p : K) = 0 := schemeScalarPresheaf_primeCast N δ p hR (op ⊤)
  let f0 := pullback.snd g δ ≫ N.isoSpec.hom
  haveI : IsAffineHom (pullback.fst g δ) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback g δ).flip
      (inferInstance : IsAffineHom δ)
  let W (j : κ) := pullback.fst g δ ⁻¹ᵁ V j
  have hW (j) : IsAffineOpen (W j) := (hV j).preimage (pullback.fst g δ)
  have hcW : (⨆ j, W j) = ⊤ := (pullback.fst g δ).iSup_preimage_eq_top hcV
  have hd0 : PerfectCechUniversalDescent p hp f0 :=
    (perfectCechUniversalDescent_targetIso p hp (pullback.snd g δ) N.isoSpec).mpr
      (hd (n+1) (Nat.zero_lt_succ n))
  let F0 : Arrow.mk (pullback.snd f0 (𝟙 (Spec (CommRingCat.of K)))) ⟶ Arrow.mk f0 :=
    Arrow.homMk (pullback.fst f0 (𝟙 _)) (𝟙 _) pullback.condition
  haveI : IsIso F0.left := by change IsIso (pullback.fst f0 (𝟙 _)); infer_instance
  haveI : IsIso F0.right := by change IsIso (𝟙 (Spec (CommRingCat.of K))); infer_instance
  have H0 : IsPullback F0.left (pullback.snd f0 (𝟙 (Spec (CommRingCat.of K)))) f0 F0.right :=
    IsPullback.of_hasPullback f0 (𝟙 _)
  have hbase0 : F0.right = Spec.map (CommRingCat.ofHom (RingHom.id K)) := (Spec.map_id _).symm
  have hPC := (nilBaseChange_tupleTotal_acyclic_iff
    (pullback.snd f0 (𝟙 (Spec (CommRingCat.of K)))) f0 F0 H0 (RingHom.id K) hbase0
      p hp hK hK W hW).mpr
        (hd0 K hK (𝟙 _) κ (fun j ↦ F0.left ⁻¹ᵁ W j)
          (fun j ↦ (hW j).preimage F0.left) (F0.left.iSup_preimage_eq_top hcW))
  let F : Arrow.mk f0 ⟶ Arrow.mk g := Arrow.homMk (pullback.fst g δ)
    (N.isoSpec.inv ≫ δ) (by simp [f0, Category.assoc, pullback.condition])
  have HF : IsPullback F.left f0 g F.right := by
    refine (IsPullback.of_hasPullback g δ).of_iso
      (Iso.refl _) (Iso.refl _) N.isoSpec (Iso.refl _) ?_ ?_ ?_ ?_ <;>
      simp [F, f0, Category.assoc]
  let NF := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.map
    (Arrow.mapAugmentedCechNerve F)
  have hb {Z : Scheme.{u}} (j : Z ⟶ Spec (CommRingCat.of K)) :
      augmentedNerveBase j .star = 𝟙 _ := by
    exact CategoryTheory.Functor.map_id _ _
  have HN (b : AugmentedSimplexCategory) :
      IsPullback (NF.app (op b)) (augmentedNerveBase f0 b)
        (augmentedNerveBase g b) F.right := by
    cases b with
    | star =>
      rw [hb f0]
      change IsPullback F.right (𝟙 _) (augmentedNerveBase g .star) F.right
      have hbg : augmentedNerveBase g .star = 𝟙 _ := CategoryTheory.Functor.map_id _ _
      rw [hbg]
      exact IsPullback.of_id_snd
    | of b => exact isPullback_cechNerve_base F HF (op b)
  have HN' (b : AugmentedSimplexCategory) :
      IsPullback (NF.app (op b)) (augmentedNerveBase f0 b ≫ N.isoSpec.inv)
        (augmentedNerveBase g b) δ := by
    refine (HN b).of_iso (Iso.refl _) (Iso.refl _) N.isoSpec.symm (Iso.refl _)
      ?_ ?_ ?_ ?_ <;> simp [F, Category.assoc]
  haveI : IsIso (augmentedNerveBase (𝟙 (Spec (CommRingCat.of K))) .star) := by
    rw [hb]; infer_instance
  let π (b : AugmentedSimplexCategory) :=
    pullback.snd (augmentedNerveBase (𝟙 (Spec (CommRingCat.of K))) .star)
      (augmentedNerveBase f0 b)
  let e (b : AugmentedSimplexCategory) := asIso (π b) ≪≫ (HN' b).flip.isoPullback
  have efst (b) : (e b).hom ≫ pullback.fst δ (augmentedNerveBase g b) =
      π b ≫ augmentedNerveBase f0 b ≫ N.isoSpec.inv := by
    dsimp only [e]
    rw [Iso.trans_hom, Category.assoc, (HN' b).flip.isoPullback_hom_fst]
    rfl
  have esnd (b) : (e b).hom ≫ pullback.snd δ (augmentedNerveBase g b) =
      π b ≫ NF.app (op b) := by
    dsimp only [e]
    rw [Iso.trans_hom, Category.assoc, (HN' b).flip.isoPullback_hom_snd]
    rfl
  let S := (Functor.curryObj (pairedPerfectCech (𝟙 (Spec (CommRingCat.of K))) f0
    (fun _ : Unit ↦ ⊤) W p hp hK)).obj (WithInitial.star : AugmentedSimplexCategory)
  let T := (Functor.curryObj (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR)).obj a
  let Us (b) := pairedCechOpen (𝟙 (Spec (CommRingCat.of K))) f0 (fun _ : Unit ↦ ⊤) W .star b
  let Ut (b) := pairedCechOpen h g (fun _ : Unit ↦ ⊤) V a b
  let hS (b) := pairedCechPrimeCast (𝟙 (Spec (CommRingCat.of K))) f0 p hK .star b
  let hT (b) := pairedCechPrimeCast h g p hR a b
  let ρ (b : AugmentedSimplexCategory)
      (t : (Fin (augmentedTupleLength a) → Unit) × (Fin (augmentedTupleLength b) → κ)) :
      (Fin 0 → Unit) × (Fin (augmentedTupleLength b) → κ) := (fun _ ↦ (), t.2)
  let σ (b : AugmentedSimplexCategory)
      (t : (Fin 0 → Unit) × (Fin (augmentedTupleLength b) → κ)) :
      (Fin (augmentedTupleLength a) → Unit) × (Fin (augmentedTupleLength b) → κ) :=
    (fun _ ↦ (), t.2)
  have hρσ (b) : ρ b ∘ σ b = id := by
    funext t; exact Prod.ext (Subsingleton.elim _ _) rfl
  have hσρ (b) : σ b ∘ ρ b = id := by
    funext t; exact Prod.ext (Subsingleton.elim _ _) rfl
  have htop {B : Type u} [CommRing B] {Z : Scheme.{u}}
      (j : Z ⟶ Spec (CommRingCat.of B)) (b : AugmentedSimplexCategory)
      (t : Fin (augmentedTupleLength b) → Unit) :
      augmentedTupleOpen j (fun _ : Unit ↦ ⊤) b t = ⊤ := by
    cases b <;> simp [augmentedTupleOpen, schemeCechTupleOpen]
  have hWb (b) (t : Fin (augmentedTupleLength b) → κ) :
      augmentedTupleOpen f0 W b t = NF.app (op b) ⁻¹ᵁ augmentedTupleOpen g V b t := by
    cases b with
    | star => simp [augmentedTupleOpen]
    | of b => exact schemeCechTupleOpen_mapCechNerve_preimage F V (op b) t
  have hcov (b) (t : (Fin 0 → Unit) × (Fin (augmentedTupleLength b) → κ)) :
      Us b t = (e b).hom ⁻¹ᵁ Ut b (σ b t) := by
    dsimp only [Us, Ut, pairedCechOpen]
    rw [htop, htop, Scheme.Hom.preimage_top, Scheme.Hom.preimage_top,
      top_inf_eq, top_inf_eq, hWb, ← Scheme.Hom.comp_preimage,
      ← Scheme.Hom.comp_preimage, esnd]
  have hback (b) (t : (Fin (augmentedTupleLength a) → Unit) ×
      (Fin (augmentedTupleLength b) → κ)) : Ut b t = (e b).inv ⁻¹ᵁ Us b (ρ b t) := by
    rw [hcov, ← Scheme.Hom.comp_preimage, (e b).inv_hom_id, Scheme.Hom.id_preimage]
  let m (b) : S.obj b ⟶ T.obj b :=
    schemeStructurePerfectCechRefinedPullbackMap (e b).inv p hp (hS b) (hT b)
      (Us b) (Ut b) (ρ b) (fun t ↦ le_of_eq (hback b t))
  have hm (b) : IsIso (m b) := by
    let r := schemeStructurePerfectCechRefinedPullbackMap (e b).hom p hp (hT b) (hS b)
      (Ut b) (Us b) (σ b) (fun t ↦ le_of_eq (hcov b t))
    have hwS (t) : Us b t ≤ (𝟙 (pairedCechScheme (𝟙 (Spec (CommRingCat.of K))) f0 .star b)) ⁻¹ᵁ Us b ((ρ b ∘ σ b) t) := by
      rw [hρσ, Scheme.Hom.id_preimage]
      exact le_rfl
    have hwT (t) : Ut b t ≤ (𝟙 (pairedCechScheme h g a b)) ⁻¹ᵁ Ut b ((σ b ∘ ρ b) t) := by
      rw [hσρ, Scheme.Hom.id_preimage]
      exact le_rfl
    have h₁ : m b ≫ r = 𝟙 _ :=
      (schemeStructurePerfectCechRefinedPullbackMap_compIndex (e b).inv (e b).hom
        (𝟙 _) (e b).hom_inv_id p hp (hS b) (hT b) (hS b)
        (Us b) (Ut b) (Us b) (ρ b) (σ b)
        (fun t ↦ le_of_eq (hback b t)) (fun t ↦ le_of_eq (hcov b t)) hwS).trans
          (schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq (𝟙 _) rfl p hp (hS b)
            (Us b) (ρ b ∘ σ b) (hρσ b) hwS)
    have h₂ : r ≫ m b = 𝟙 _ :=
      (schemeStructurePerfectCechRefinedPullbackMap_compIndex (e b).hom (e b).inv
        (𝟙 _) (e b).inv_hom_id p hp (hT b) (hS b) (hT b)
        (Ut b) (Us b) (Ut b) (σ b) (ρ b)
        (fun t ↦ le_of_eq (hcov b t)) (fun t ↦ le_of_eq (hback b t)) hwT).trans
          (schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq (𝟙 _) rfl p hp (hT b)
            (Ut b) (σ b ∘ ρ b) (hσρ b) hwT)
    exact ⟨⟨r, h₁, h₂⟩⟩
  let η : S ⟶ T :=
    { app := m
      naturality := fun {b c} α ↦ by
        let s := pairedCechSchemeMap (𝟙 (Spec (CommRingCat.of K))) f0
          (𝟙 (WithInitial.star : AugmentedSimplexCategory)) α
        let t := pairedCechSchemeMap h g (𝟙 a) α
        have hπ : s ≫ π b = π c ≫
            (AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
              (Arrow.mk f0).augmentedCechNerve).map α.op := by
          dsimp only [s, π, pairedCechSchemeMap, pullback.map]
          exact pullback.lift_snd _ _ _
        have hbNat : (AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
              (Arrow.mk f0).augmentedCechNerve).map α.op ≫ augmentedNerveBase f0 b =
            augmentedNerveBase f0 c := by
          unfold augmentedNerveBase
          rw [← CategoryTheory.Functor.map_comp]
          congr 1
        let L := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
          (Arrow.mk f0).augmentedCechNerve
        let G := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
          (Arrow.mk g).augmentedCechNerve
        have htF : t ≫ pullback.fst δ (augmentedNerveBase g b) =
            pullback.fst δ (augmentedNerveBase g c) := by
          dsimp only [t, pairedCechSchemeMap, pullback.map]
          rw [pullback.lift_fst]
          rw [show (𝟙 a).op = 𝟙 (op a) from rfl, CategoryTheory.Functor.map_id,
            Category.comp_id]
        have htS : t ≫ pullback.snd δ (augmentedNerveBase g b) =
            pullback.snd δ (augmentedNerveBase g c) ≫ G.map α.op := by
          dsimp only [t, pairedCechSchemeMap, pullback.map, G]
          exact pullback.lift_snd _ _ _
        have hn : s ≫ (e b).hom = (e c).hom ≫ t := by
          apply pullback.hom_ext
          · calc
              (s ≫ (e b).hom) ≫ pullback.fst δ (augmentedNerveBase g b) =
                  s ≫ π b ≫ augmentedNerveBase f0 b ≫ N.isoSpec.inv := by
                    rw [Category.assoc, efst]
              _ = π c ≫ (L.map α.op ≫ augmentedNerveBase f0 b) ≫ N.isoSpec.inv := by
                    rw [← Category.assoc s (π b), hπ]
                    simp only [Category.assoc, L]
              _ = π c ≫ augmentedNerveBase f0 c ≫ N.isoSpec.inv := by rw [hbNat]
              _ = ((e c).hom ≫ t) ≫ pullback.fst δ (augmentedNerveBase g b) := by
                    rw [Category.assoc, htF, efst]
          · calc
              (s ≫ (e b).hom) ≫ pullback.snd δ (augmentedNerveBase g b) =
                  s ≫ π b ≫ NF.app (op b) := by rw [Category.assoc, esnd]
              _ = π c ≫ (L.map α.op ≫ NF.app (op b)) := by
                    rw [← Category.assoc s (π b), hπ]
                    simp only [Category.assoc, L]
              _ = π c ≫ NF.app (op c) ≫ G.map α.op := by
                    rw [show L.map α.op ≫ NF.app (op b) = NF.app (op c) ≫ G.map α.op
                      from NF.naturality α.op]
              _ = ((e c).hom ≫ t) ≫ pullback.snd δ (augmentedNerveBase g b) := by
                    symm
                    calc
                      ((e c).hom ≫ t) ≫ pullback.snd δ (augmentedNerveBase g b) =
                          ((e c).hom ≫ pullback.snd δ (augmentedNerveBase g c)) ≫ G.map α.op := by
                            rw [Category.assoc, htS, ← Category.assoc]
                      _ = (π c ≫ NF.app (op c)) ≫ G.map α.op :=
                        congrArg (fun z ↦ z ≫ G.map α.op) (esnd c)
                      _ = _ := Category.assoc _ _ _
        let k := (e c).inv ≫ s
        have hk : t ≫ (e b).inv = k := by
          apply (cancel_mono (e b).hom).mp
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
          dsimp only [k]
          rw [Category.assoc, hn, Iso.inv_hom_id_assoc]
        let γS (x : (Fin 0 → Unit) × (Fin (augmentedTupleLength c) → κ)) :=
          (x.1 ∘ augmentedTupleIndexMap (𝟙 (WithInitial.star : AugmentedSimplexCategory)),
            x.2 ∘ augmentedTupleIndexMap α)
        let γT (x : (Fin (augmentedTupleLength a) → Unit) × (Fin (augmentedTupleLength c) → κ)) :=
          (x.1 ∘ augmentedTupleIndexMap (𝟙 a), x.2 ∘ augmentedTupleIndexMap α)
        have hSmap (x) : Us c x ≤ s ⁻¹ᵁ Us b (γS x) :=
          pairedCechOpen_map_le (𝟙 (Spec (CommRingCat.of K))) f0
            (fun _ : Unit ↦ ⊤) W (𝟙 (WithInitial.star : AugmentedSimplexCategory)) α x
        have hTmap (x) : Ut c x ≤ t ⁻¹ᵁ Ut b (γT x) :=
          pairedCechOpen_map_le h g (fun _ : Unit ↦ ⊤) V (𝟙 a) α x
        have hc (x : (Fin (augmentedTupleLength a) → Unit) × (Fin (augmentedTupleLength c) → κ)) :
            Ut c x ≤ k ⁻¹ᵁ Us b (γS (ρ c x)) := by
          rw [show k = (e c).inv ≫ s from rfl, Scheme.Hom.comp_preimage]
          exact (le_of_eq (hback c x)).trans ((e c).inv.preimage_mono (hSmap (ρ c x)))
        have hc' (x : (Fin (augmentedTupleLength a) → Unit) × (Fin (augmentedTupleLength c) → κ)) :
            Ut c x ≤ k ⁻¹ᵁ Us b (ρ b (γT x)) := by
          change Ut c x ≤ k ⁻¹ᵁ Us b (γS (ρ c x))
          exact hc x
        have hl := schemeStructurePerfectCechRefinedPullbackMap_compIndex
          s (e c).inv k rfl p hp (hS b) (hS c) (hT c)
          (Us b) (Us c) (Ut c) γS (ρ c) hSmap (fun x ↦ le_of_eq (hback c x)) hc
        have hr := schemeStructurePerfectCechRefinedPullbackMap_compIndex
          (e b).inv t k hk p hp (hS b) (hT b) (hT c)
          (Us b) (Ut b) (Ut c) (ρ b) γT (fun x ↦ le_of_eq (hback b x)) hTmap hc'
        exact hl.trans hr.symm }
  haveI : ∀ b, IsIso (η.app b) := hm
  haveI : IsIso η := NatIso.isIso_of_isIso_app _
  let ea := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.mapIso (asIso η)
  let et := cechIntegerLiftTotalFunctor.mapIso (SerrePositivity.Cech.augmentedCochain.mapIso ea)
  have hs := (pairedPerfectCech_zero_col_acyclic_iff (𝟙 (Spec (CommRingCat.of K))) f0
    (fun _ : Unit ↦ ⊤) W p hp hK).mpr hPC
  exact fun b ↦ (hs b).of_iso et

end SerrePositivity.AlgebraicGeometry
