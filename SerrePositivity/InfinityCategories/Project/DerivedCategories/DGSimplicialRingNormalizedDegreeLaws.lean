module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingNormalizedDegreeProduct
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGSimplicialRingProjectedLaws
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite AlgebraicTopology AlgebraicTopology.DoldKan HomologicalComplex
open scoped _root_.Simplicial
variable (A : SimplicialObject RingCat.{u})
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A
local notation "N" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A
local notation "I" => inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)
lemma simplicialRingNormalizedInclusion_degreeMap {m n : ℕ} (h : m = n) (x : (N).X n) :
    ((I).f m).hom ((eqToHom (congrArg (fun k ↦ (N).X k) h.symm)).hom x) =
      (A.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ringShuffleDegreeMap h).op).hom (((I).f n).hom x) := by
  cases h
  change ((I).f m).hom x = (A.map (𝟙 (op ⦋m⦌))).hom (((I).f m).hom x)
  rw [A.map_id]
  rfl
lemma simplicialRingNormalizedDegreeProduct_left_unit (q : ℕ) (y : (N).X q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A 0 q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedOne A) y =
      (eqToHom (congrArg (fun k ↦ (N).X k) (Nat.zero_add q).symm)).hom y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedInclusion_injective A (0 + q)
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct_inclusion A 0 q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedOne A) y
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedOne_inclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct_left_unit] at h
  have hp := congrArg (fun f ↦ (f.f q).hom y) (inclusionOfMooreComplexMap_comp_PInfty C)
  calc
    _ = ((PInfty (X := C)).f (0 + q)).hom
      ((A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.zeroLeftShuffleDegreeMap q).op).hom (((I).f q).hom y)) := h
    _ = (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.zeroLeftShuffleDegreeMap q).op).hom
      (((PInfty (X := C)).f q).hom (((I).f q).hom y)) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ringNormalizedProjection_degreeMap A (Nat.zero_add q) _
    _ = (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.zeroLeftShuffleDegreeMap q).op).hom (((I).f q).hom y) :=
      congrArg (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.zeroLeftShuffleDegreeMap q).op).hom hp
    _ = _ := (simplicialRingNormalizedInclusion_degreeMap A (Nat.zero_add q) y).symm
lemma simplicialRingNormalizedDegreeProduct_assoc (p q r : ℕ)
    (x : (N).X p) (y : (N).X q) (z : (N).X r) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A (p + q) r
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A p q x y) z =
    (eqToHom (congrArg (fun k ↦ (N).X k) (Nat.add_assoc p q r).symm)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A p (q + r) x
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A q r y z)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedInclusion_injective A (p + q + r)
  have hL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct_inclusion A (p + q) r
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A p q x y) z
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct_inclusion A p q x y] at hL
  have hR := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct_inclusion A p (q + r) x
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A q r y z)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct_inclusion A q r y z] at hR
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.projectedRingShuffleProduct_assoc A p q r
    (((I).f p).hom x) (((I).f q).hom y) (((I).f r).hom z)
  have hcast := simplicialRingNormalizedInclusion_degreeMap A (Nat.add_assoc p q r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A p (q + r) x
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A q r y z))
  exact hL.trans (h.trans ((congrArg
    (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.associationMap p q r).op).hom hR).symm.trans hcast.symm))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
