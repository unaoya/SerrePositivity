module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleRightCenterComponents

/-!
概要：同じ中心側の次数ごとの二つの比較射が互いに逆である。
方針：元の各ιTotalで中心とEの包含・射影を消去する。
規約：鎖写像性は後で照合し、ここでは同じ各次数の恒等式だけを示す。
使われ方：元の右側のwhole totalのunsigned successorとの比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Preadditive
open scoped Simplicial ZeroObject
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

private theorem cechCenter_sign_sq (b : ℕ) : (-1 : ℤ) ^ b * (-1 : ℤ) ^ b = 1 := by
  rw [← mul_pow]
  simp

set_option backward.isDefEq.respectTransparency false in
private def cechRightCenterVertexIso (a b : ℕ) :
    ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).X a).X b ≅
      ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).X a).X (b + 1) := by
  let K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
    schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS
  let L : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
    schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS
  let s := schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌
  let t := schemePerfectCechTupleSquare f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS ⦋a⦌
  let pc (b : ℕ) : (K.X a).X (b + 1) ⟶ s.E.X b := t.leftCπ b
  let ic (b : ℕ) : s.E.X b ⟶ (K.X a).X (b + 1) := t.leftCι b
  let ie (b : ℕ) : s.E.X b ⟶ (L.X a).X (b + 2) := s.rightEι b
  let pe (b : ℕ) : (L.X a).X (b + 2) ⟶ s.E.X b := s.rightEπ b
  refine
    { hom := schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS a b
      inv := schemePerfectCechTupleRightCenterBackwardVertex f g F q hq U p hp hR hS a b
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · cases b with
    | zero =>
      change (-s.rightCenterι) ≫ (-s.rightCenterπ) = 𝟙 _
      rw [neg_comp, comp_neg, neg_neg, CechAugmentedSquare.rightCenterι_π]
    | succ b =>
      change (((-1 : ℤ) ^ b) • (pc b ≫ ie b)) ≫ (((-1 : ℤ) ^ b) • (pe b ≫ ic b)) = 𝟙 _
      rw [zsmul_comp, comp_zsmul, smul_smul, cechCenter_sign_sq, one_smul]
      have hE : ie b ≫ pe b = 𝟙 _ := s.rightEι_π b
      have hC : pc b ≫ ic b = 𝟙 _ := t.leftCπ_ι b
      rw [Category.assoc, ← Category.assoc (ie b), hE, Category.id_comp, hC]
  · cases b with
    | zero =>
      change (-s.rightCenterπ) ≫ (-s.rightCenterι) = 𝟙 _
      rw [neg_comp, comp_neg, neg_neg, CechAugmentedSquare.rightCenterπ_ι]
    | succ b =>
      change (((-1 : ℤ) ^ b) • (pe b ≫ ic b)) ≫ (((-1 : ℤ) ^ b) • (pc b ≫ ie b)) = 𝟙 _
      rw [zsmul_comp, comp_zsmul, smul_smul, cechCenter_sign_sq, one_smul]
      have hC : ic b ≫ pc b = 𝟙 _ := t.leftCι_π b
      have hE : pe b ≫ ie b = 𝟙 _ := s.rightEπ_ι b
      rw [Category.assoc, ← Category.assoc (ic b), hC, Category.id_comp, hE]

set_option backward.isDefEq.respectTransparency false in
/-- 中心の同じ左側の各全次数で、前向き射の後に逆向き射を取ると恒等射。 -/
theorem schemePerfectCechTupleRightCenterForward_backward (n : ℕ) :
    schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS n ≫
      schemePerfectCechTupleRightCenterBackwardComponent f g F q hq U p hp hR hS n = 𝟙 _ := by
  let K := schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS
  let L := schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, ι_schemePerfectCechTupleRightCenterForwardComponent, Category.comp_id]
  let α : (K.X a).X b ⟶ (L.X a).X (b + 1) :=
    schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS a b
  let β : (L.X a).X (b + 1) ⟶ (K.X a).X b :=
    schemePerfectCechTupleRightCenterBackwardVertex f g F q hq U p hp hR hS a b
  let i := K.ιTotal up a b n h
  let hj : ComplexShape.π up up up (a, b + 1) = n + 1 := by
    change a + b = n at h
    change a + (b + 1) = n + 1
    omega
  let j := L.ιTotal up a (b + 1) (n + 1) hj
  change (α ≫ j) ≫ schemePerfectCechTupleRightCenterBackwardComponent f g F q hq U p hp hR hS n = i
  have hh : j ≫ schemePerfectCechTupleRightCenterBackwardComponent f g F q hq U p hp hR hS n = β ≫ i :=
    ι_schemePerfectCechTupleRightCenterBackwardComponent f g F q hq U p hp hR hS a (b + 1) n hj
  have hv : α ≫ β = 𝟙 _ :=
    (cechRightCenterVertexIso f g F q hq U p hp hR hS a b).hom_inv_id
  calc
    _ = α ≫ (j ≫ schemePerfectCechTupleRightCenterBackwardComponent f g F q hq U p hp hR hS n) :=
      Category.assoc _ _ _
    _ = α ≫ (β ≫ i) := congrArg (fun z : (L.X a).X (b + 1) ⟶ (K.total up).X n ↦ α ≫ z) hh
    _ = i := by rw [← Category.assoc, hv, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- 元の右側の同じ正の全次数でも、逆向き射の後に前向き射を取ると恒等射。 -/
theorem schemePerfectCechTupleRightCenterBackward_forward (n : ℕ) :
    schemePerfectCechTupleRightCenterBackwardComponent f g F q hq U p hp hR hS n ≫
      schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS n = 𝟙 _ := by
  let K := schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS
  let L := schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, ι_schemePerfectCechTupleRightCenterBackwardComponent, Category.comp_id]
  cases b with
  | zero =>
    have hz : IsZero ((L.X a).X 0) := by
      change IsZero (0 : ModuleCat.{u} ℤ)
      exact isZero_zero _
    exact hz.eq_of_src _ _
  | succ b =>
    let α : (K.X a).X b ⟶ (L.X a).X (b + 1) :=
      schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS a b
    let β : (L.X a).X (b + 1) ⟶ (K.X a).X b :=
      schemePerfectCechTupleRightCenterBackwardVertex f g F q hq U p hp hR hS a b
    let hi : ComplexShape.π up up up (a, b) = n := by
      change a + (b + 1) = n + 1 at h
      change a + b = n
      omega
    let i := K.ιTotal up a b n hi
    let j := L.ιTotal up a (b + 1) (n + 1) h
    change (β ≫ i) ≫ schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS n = j
    have hh : i ≫ schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS n = α ≫ j :=
      ι_schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS a b n hi
    have hv : β ≫ α = 𝟙 _ :=
      (cechRightCenterVertexIso f g F q hq U p hp hR hS a b).inv_hom_id
    calc
      _ = β ≫ (i ≫ schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS n) :=
        Category.assoc _ _ _
      _ = β ≫ (α ≫ j) := congrArg (fun z : (K.X a).X b ⟶ (L.total up).X (n + 1) ↦ β ≫ z) hh
      _ = j := by rw [← Category.assoc, hv, Category.id_comp]

end SerrePositivity.AlgebraicGeometry
