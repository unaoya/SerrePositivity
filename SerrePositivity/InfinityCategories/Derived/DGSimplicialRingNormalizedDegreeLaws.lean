module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingNormalizedDegreeProduct
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingProjectedLaws
/-!
概要：元の Moore 部分複体の実乗法の左単位・結合則。
方針：実包含の単射性、同じ射影乗法と次数移送の整合性を使う。
規約：元の実 tensor 乗法を保持する。使われ方：β5(g) の正規化 dg 代数化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite AlgebraicTopology AlgebraicTopology.DoldKan HomologicalComplex
open scoped Simplicial
variable (A : SimplicialObject RingCat.{u})
local notation "C" => simplicialRingIntegerModule A
local notation "N" => simplicialRingNormalizedChains A
local notation "I" => inclusionOfMooreComplexMap (simplicialRingIntegerModule A)
lemma simplicialRingNormalizedInclusion_degreeMap {m n : ℕ} (h : m = n) (x : (N).X n) :
    ((I).f m).hom ((eqToHom (congrArg (fun k ↦ (N).X k) h.symm)).hom x) =
      (A.map (ringShuffleDegreeMap h).op).hom (((I).f n).hom x) := by
  cases h
  change ((I).f m).hom x = (A.map (𝟙 (op ⦋m⦌))).hom (((I).f m).hom x)
  rw [A.map_id]
  rfl
lemma simplicialRingNormalizedDegreeProduct_left_unit (q : ℕ) (y : (N).X q) :
    simplicialRingNormalizedDegreeProduct A 0 q (simplicialRingNormalizedOne A) y =
      (eqToHom (congrArg (fun k ↦ (N).X k) (Nat.zero_add q).symm)).hom y := by
  apply simplicialRingNormalizedInclusion_injective A (0 + q)
  have h := simplicialRingNormalizedDegreeProduct_inclusion A 0 q
    (simplicialRingNormalizedOne A) y
  rw [simplicialRingNormalizedOne_inclusion, simplicialRingShuffleProduct_left_unit] at h
  have hp := congrArg (fun f ↦ (f.f q).hom y) (inclusionOfMooreComplexMap_comp_PInfty C)
  calc
    _ = ((PInfty (X := C)).f (0 + q)).hom
      ((A.map (zeroLeftShuffleDegreeMap q).op).hom (((I).f q).hom y)) := h
    _ = (A.map (zeroLeftShuffleDegreeMap q).op).hom
      (((PInfty (X := C)).f q).hom (((I).f q).hom y)) :=
        ringNormalizedProjection_degreeMap A (Nat.zero_add q) _
    _ = (A.map (zeroLeftShuffleDegreeMap q).op).hom (((I).f q).hom y) :=
      congrArg (A.map (zeroLeftShuffleDegreeMap q).op).hom hp
    _ = _ := (simplicialRingNormalizedInclusion_degreeMap A (Nat.zero_add q) y).symm
lemma simplicialRingNormalizedDegreeProduct_assoc (p q r : ℕ)
    (x : (N).X p) (y : (N).X q) (z : (N).X r) :
    simplicialRingNormalizedDegreeProduct A (p + q) r
      (simplicialRingNormalizedDegreeProduct A p q x y) z =
    (eqToHom (congrArg (fun k ↦ (N).X k) (Nat.add_assoc p q r).symm)).hom
      (simplicialRingNormalizedDegreeProduct A p (q + r) x
        (simplicialRingNormalizedDegreeProduct A q r y z)) := by
  apply simplicialRingNormalizedInclusion_injective A (p + q + r)
  have hL := simplicialRingNormalizedDegreeProduct_inclusion A (p + q) r
    (simplicialRingNormalizedDegreeProduct A p q x y) z
  rw [simplicialRingNormalizedDegreeProduct_inclusion A p q x y] at hL
  have hR := simplicialRingNormalizedDegreeProduct_inclusion A p (q + r) x
    (simplicialRingNormalizedDegreeProduct A q r y z)
  rw [simplicialRingNormalizedDegreeProduct_inclusion A q r y z] at hR
  have h := projectedRingShuffleProduct_assoc A p q r
    (((I).f p).hom x) (((I).f q).hom y) (((I).f r).hom z)
  have hcast := simplicialRingNormalizedInclusion_degreeMap A (Nat.add_assoc p q r)
    (simplicialRingNormalizedDegreeProduct A p (q + r) x
      (simplicialRingNormalizedDegreeProduct A q r y z))
  exact hL.trans (h.trans ((congrArg
    (A.map (NormalizedRingShuffle.associationMap p q r).op).hom hR).symm.trans hcast.symm))
end SerrePositivity.InfinityCategories
