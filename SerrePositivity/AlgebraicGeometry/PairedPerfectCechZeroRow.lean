module

public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechZeroAxes

/-!
概要：実際の二変数Čech図式の零次行と元の構造射のタプルtotalを比較する。
方針：pullbackの対称同型と添字交換を増大点を含む自然同型にし、P20を使う。
規約：元の係数・被覆・増大を保持し、両方向の完全性を示す。
使われ方：相対fppfの軸比較（承認済み計画P21）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false

/-- 実際の二因子の対称同型により、零次行の完全性を元のhのタプルtotalと比較する。 -/
theorem pairedPerfectCech_zero_row_acyclic_iff
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj
        (SerrePositivity.Cech.row (pairedPerfectCech h g U V p hp hR) 0)) up).Acyclic ↔
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble h U p hp hR) up).Acyclic := by
  let S := (Functor.curryObj (pairedPerfectCech g h V U p hp hR)).obj
    (WithInitial.star : AugmentedSimplexCategory)
  let T := (Functor.curryObj (pairedPerfectCech h g U V p hp hR)).flip.obj
    (WithInitial.star : AugmentedSimplexCategory)
  let B (a : AugmentedSimplexCategory) := pairedCechScheme g h .star a
  let C (a : AugmentedSimplexCategory) := pairedCechScheme h g a .star
  let Us (a : AugmentedSimplexCategory) := pairedCechOpen g h V U .star a
  let Ut (a : AugmentedSimplexCategory) := pairedCechOpen h g U V a .star
  let hs (a : AugmentedSimplexCategory) := pairedCechPrimeCast g h p hR .star a
  let ht (a : AugmentedSimplexCategory) := pairedCechPrimeCast h g p hR a .star
  let e (a : AugmentedSimplexCategory) :=
    pullbackSymmetry (augmentedNerveBase h a) (augmentedNerveBase g .star)
  have hcov (a : AugmentedSimplexCategory)
      (t : (Fin (augmentedTupleLength a) → ι) × (Fin 0 → κ)) :
      Ut a t = (e a).hom ⁻¹ᵁ Us a t.swap := by
    dsimp only [Ut, Us, e, pairedCechOpen]
    rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullbackSymmetry_hom_comp_fst, ← Scheme.Hom.comp_preimage,
      pullbackSymmetry_hom_comp_snd]
    exact inf_comm _ _
  have hback (a : AugmentedSimplexCategory)
      (t : (Fin 0 → κ) × (Fin (augmentedTupleLength a) → ι)) :
      Us a t ≤ (e a).inv ⁻¹ᵁ Ut a t.swap := by
    rw [hcov, ← Scheme.Hom.comp_preimage, (e a).inv_hom_id, Scheme.Hom.id_preimage]
    exact le_of_eq (congrArg (Us a) (Prod.swap_swap t).symm)
  let m (a : AugmentedSimplexCategory) : S.obj a ⟶ T.obj a :=
    schemeStructurePerfectCechRefinedPullbackMap (e a).hom p hp (hs a) (ht a)
      (Us a) (Ut a) Prod.swap (fun t ↦ le_of_eq (hcov a t))
  have hm (a : AugmentedSimplexCategory) : IsIso (m a) := by
    let r := schemeStructurePerfectCechRefinedPullbackMap (e a).inv p hp (ht a) (hs a)
      (Ut a) (Us a) Prod.swap (hback a)
    have hUW₁ (t : (Fin 0 → κ) × (Fin (augmentedTupleLength a) → ι)) :
        Us a t ≤ (𝟙 (B a)) ⁻¹ᵁ Us a t.swap.swap := by
      rw [Scheme.Hom.id_preimage]
      exact le_of_eq (congrArg _ (Prod.swap_swap t).symm)
    have hUW₂ (t : (Fin (augmentedTupleLength a) → ι) × (Fin 0 → κ)) :
        Ut a t ≤ (𝟙 (C a)) ⁻¹ᵁ Ut a t.swap.swap := by
      rw [Scheme.Hom.id_preimage]
      exact le_of_eq (congrArg _ (Prod.swap_swap t).symm)
    have h₁ : m a ≫ r = 𝟙 _ := by
      exact (schemeStructurePerfectCechRefinedPullbackMap_compIndex
        (e a).hom (e a).inv (𝟙 (B a)) (e a).inv_hom_id p hp (hs a) (ht a) (hs a)
        (Us a) (Ut a) (Us a) Prod.swap Prod.swap (fun t ↦ le_of_eq (hcov a t)) (hback a)
        hUW₁).trans (schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq
          (𝟙 (B a)) rfl p hp (hs a) (Us a) (Prod.swap ∘ Prod.swap) rfl hUW₁)
    have h₂ : r ≫ m a = 𝟙 _ := by
      exact (schemeStructurePerfectCechRefinedPullbackMap_compIndex
        (e a).inv (e a).hom (𝟙 (C a)) (e a).hom_inv_id p hp (ht a) (hs a) (ht a)
        (Ut a) (Us a) (Ut a) Prod.swap Prod.swap (hback a) (fun t ↦ le_of_eq (hcov a t))
        hUW₂).trans (schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq
          (𝟙 (C a)) rfl p hp (ht a) (Ut a) (Prod.swap ∘ Prod.swap) rfl hUW₂)
    exact ⟨⟨r, h₁, h₂⟩⟩
  let η : S ⟶ T :=
    { app := m
      naturality := fun {a b} α ↦ by
        let s := pairedCechSchemeMap g h (𝟙 (WithInitial.star : AugmentedSimplexCategory)) α
        let t := pairedCechSchemeMap h g α (𝟙 (WithInitial.star : AugmentedSimplexCategory))
        let k := (e b).hom ≫ s
        let ρ (x : (Fin 0 → κ) × (Fin (augmentedTupleLength b) → ι)) :=
          (x.1 ∘ augmentedTupleIndexMap (𝟙 (WithInitial.star : AugmentedSimplexCategory)),
            x.2 ∘ augmentedTupleIndexMap α)
        let σ (x : (Fin (augmentedTupleLength b) → ι) × (Fin 0 → κ)) :=
          (x.1 ∘ augmentedTupleIndexMap α,
            x.2 ∘ augmentedTupleIndexMap (𝟙 (WithInitial.star : AugmentedSimplexCategory)))
        have hk : t ≫ (e a).hom = k := by
          apply pullback.hom_ext <;>
            simp [t, k, s, e, pairedCechSchemeMap, pullback.map, Category.assoc]
        have hρ (x) : Us b x ≤ s ⁻¹ᵁ Us a (ρ x) :=
          pairedCechOpen_map_le g h V U (𝟙 (WithInitial.star : AugmentedSimplexCategory)) α x
        have hσ (x) : Ut b x ≤ t ⁻¹ᵁ Ut a (σ x) :=
          pairedCechOpen_map_le h g U V α (𝟙 (WithInitial.star : AugmentedSimplexCategory)) x
        have hidx : Prod.swap ∘ σ = ρ ∘ Prod.swap := by funext x; rfl
        have hc (x : (Fin (augmentedTupleLength b) → ι) × (Fin 0 → κ)) :
            Ut b x ≤ k ⁻¹ᵁ Us a (ρ x.swap) := by
          rw [show k = (e b).hom ≫ s from rfl, Scheme.Hom.comp_preimage]
          exact (le_of_eq (hcov b x)).trans ((e b).hom.preimage_mono (hρ x.swap))
        have hc' (x : (Fin (augmentedTupleLength b) → ι) × (Fin 0 → κ)) :
            Ut b x ≤ k ⁻¹ᵁ Us a (σ x).swap := by
          change Ut b x ≤ k ⁻¹ᵁ Us a (ρ x.swap)
          exact hc x
        have hleft := schemeStructurePerfectCechRefinedPullbackMap_compIndex
          s (e b).hom k rfl p hp (hs a) (hs b) (ht b)
          (Us a) (Us b) (Ut b) ρ Prod.swap hρ (fun x ↦ le_of_eq (hcov b x)) hc
        have hright := schemeStructurePerfectCechRefinedPullbackMap_compIndex
          (e a).hom t k hk p hp (hs a) (ht a) (ht b)
          (Us a) (Ut a) (Ut b) Prod.swap σ (fun x ↦ le_of_eq (hcov a x)) hσ hc'
        exact hleft.trans hright.symm }
  haveI : ∀ a, IsIso (η.app a) := hm
  haveI : IsIso η := NatIso.isIso_of_isIso_app _
  let ea := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.mapIso (asIso η)
  let et := cechIntegerLiftTotalFunctor.mapIso (SerrePositivity.Cech.augmentedCochain.mapIso ea)
  constructor
  · intro H
    apply (pairedPerfectCech_zero_col_acyclic_iff g h V U p hp hR).mp
    exact fun n ↦ (H n).of_iso et.symm
  · intro H
    have Hc := (pairedPerfectCech_zero_col_acyclic_iff g h V U p hp hR).mpr H
    exact fun n ↦ (Hc n).of_iso et

end SerrePositivity.AlgebraicGeometry
