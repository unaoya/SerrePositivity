module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleRightCenterComponents
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftBaseComponents

/-!
概要：同じ中心側の比較射の縦微分の照合。
方針：元のleftCの同型で各成分の式へ戻し、元の負符号を消去する。
規約：中心の負符号とEの(-1)^bを元のまま保持する。
使われ方：同じtotalの再索引の鎖写像性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Preadditive
open scoped Simplicial
universe u v

/-- 元のCの座標の射影も、同じ四角形の射に自然。 -/
theorem CechAugmentedSquare.leftCπ_naturality {A : Type v} [CommRing A]
    {s t : CechAugmentedSquare.{u} A} (m : CechAugmentedSquare.Map s t) (b : ℕ) :
    m.onLeftSquare.totalComplexMap.f (b + 1) ≫ t.leftCπ b = s.leftCπ b ≫ m.left.f b := by
  apply (cancel_epi (s.leftCIso b).hom).mp
  change s.leftCι b ≫ (m.onLeftSquare.totalComplexMap.f (b + 1) ≫ t.leftCπ b) =
    s.leftCι b ≫ (s.leftCπ b ≫ m.left.f b)
  rw [← Category.assoc, CechAugmentedSquare.leftCι_naturality, Category.assoc,
    CechAugmentedSquare.leftCι_π, Category.comp_id, ← Category.assoc,
    CechAugmentedSquare.leftCι_π, Category.id_comp]

local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の各頂点の同じ符号つき比較は、元の縦微分と可換。 -/
theorem schemePerfectCechTupleRightCenterForwardVertex_vertical (a b : ℕ) :
    schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS a b ≫
      ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).X a).d (b + 1) (b + 2) =
    ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).X a).d b (b + 1) ≫
      schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS a (b + 1) := by
  let s := schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌
  let t := schemePerfectCechTupleSquare f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS ⦋a⦌
  cases b with
  | zero =>
    change (-s.rightCenterι) ≫ s.rightSquare.totalComplex.d 1 2 =
      t.leftSquare.totalComplex.d 0 1 ≫ (((-1 : ℤ) ^ 0) • (t.leftCπ 0 ≫ s.rightEι 0))
    rw [pow_zero, one_smul, neg_comp, CechAugmentedSquare.rightCenterι_d, neg_neg,
      ← CechAugmentedSquare.scalar_leftCι t, Category.assoc,
      ← Category.assoc (t.leftCι 0), CechAugmentedSquare.leftCι_π, Category.id_comp]
    rfl
  | succ b =>
    apply (cancel_epi (t.leftCIso b).hom).mp
    change t.leftCι b ≫ ((((-1 : ℤ) ^ b) • (t.leftCπ b ≫ s.rightEι b)) ≫
      s.rightSquare.totalComplex.d (b + 2) (b + 3)) =
      t.leftCι b ≫ (t.leftSquare.totalComplex.d (b + 1) (b + 2) ≫
        (((-1 : ℤ) ^ (b + 1)) • (t.leftCπ (b + 1) ≫ s.rightEι (b + 1))))
    rw [← Category.assoc, comp_zsmul, ← Category.assoc, CechAugmentedSquare.leftCι_π,
      Category.id_comp, zsmul_comp, CechAugmentedSquare.rightEι_d,
      ← Category.assoc, CechAugmentedSquare.leftCι_d]
    have hcπ : t.leftCι (b + 1) ≫ (t.leftCπ (b + 1) ≫ s.rightEι (b + 1)) =
        s.rightEι (b + 1) := by
      rw [← Category.assoc, CechAugmentedSquare.leftCι_π, Category.id_comp]
    simp only [comp_zsmul, zsmul_comp, neg_comp, comp_neg, Category.assoc, hcπ, pow_succ, mul_neg, mul_one,
      neg_smul, smul_neg, neg_neg] <;> rfl

end SerrePositivity.AlgebraicGeometry
