module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleRightCenterVertical

/-!
概要：同じ中心側の比較射の水平自然性と微分の照合。
方針：元の各余面でCの射影とEの包含の自然性を使い、同じ交代和を取る。
規約：元の逆像被覆と各余面写像を保持する。
使われ方：同じtotalの再索引の鎖写像性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory AlgebraicTopology Preadditive
open scoped Simplicial
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の各余面・退化の射でも同じ中心側の符号つき比較は自然。 -/
theorem schemePerfectCechTupleRightCenterForwardVertex_naturality
    {a b : SimplexCategory} (σ : a ⟶ b) (k : ℕ) :
    schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS a.len k ≫
      ((schemePerfectCechTupleSquareRightFunctor f g F q hq U p hp hR hS).map σ).f (k + 1) =
    ((schemePerfectCechTupleSquareLeftFunctor f f (𝟙 _) (RingHom.id S)
      (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS).map σ).f k ≫
      schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS b.len k := by
  let s := schemePerfectCechTupleSquare f g F q hq U p hp hR hS a
  let t := schemePerfectCechTupleSquare f g F q hq U p hp hR hS b
  let ms := schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS σ
  let sc := schemePerfectCechTupleSquare f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS a
  let tc := schemePerfectCechTupleSquare f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS b
  let mc := schemePerfectCechTupleSquare_map f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS σ
  cases k with
  | zero =>
    change (-s.rightCenterι) ≫ ms.onRightSquare.totalComplexMap.f 1 = 𝟙 _ ≫ (-t.rightCenterι)
    rw [neg_comp, CechAugmentedSquare.rightCenterι_naturality]
    simp only [Category.id_comp]
    rfl
  | succ k =>
    change (((-1 : ℤ) ^ k) • (sc.leftCπ k ≫ s.rightEι k)) ≫
      ms.onRightSquare.totalComplexMap.f (k + 2) =
      mc.onLeftSquare.totalComplexMap.f (k + 1) ≫
        (((-1 : ℤ) ^ k) • (tc.leftCπ k ≫ t.rightEι k))
    have hm : ms.right.f k = mc.left.f k := rfl
    rw [zsmul_comp, Category.assoc, CechAugmentedSquare.rightEι_naturality,
      ← Category.assoc, hm, ← CechAugmentedSquare.leftCπ_naturality,
      comp_zsmul, Category.assoc]

private theorem cechCenter_sum_f {A : Type*} [Fintype A]
    {P Q : CochainComplex (ModuleCat.{u} ℤ) ℕ} (v : A → (P ⟶ Q)) (b : ℕ) :
    (∑ i, v i).f b = ∑ i, (v i).f b :=
  map_sum (HomologicalComplex.Hom.fAddMonoidHom b) v Finset.univ

set_option backward.isDefEq.respectTransparency false in
/-- 同じ余面の交代和を取ると、元の水平微分も保たれる。 -/
theorem schemePerfectCechTupleRightCenterForwardVertex_horizontal (a b : ℕ) :
    schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS a b ≫
      ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).d a (a + 1)).f (b + 1) =
    ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).d a (a + 1)).f b ≫
      schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS (a + 1) b := by
  let L := schemePerfectCechTupleSquareRightFunctor f g F q hq U p hp hR hS
  let K := schemePerfectCechTupleSquareLeftFunctor f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS
  have hL : (schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).d a (a + 1) =
      AlternatingCofaceMapComplex.objD L a :=
    CochainComplex.of_d (fun n ↦ L.obj ⦋n⦌) (AlternatingCofaceMapComplex.objD L) a
  have hK : (schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).d a (a + 1) =
      AlternatingCofaceMapComplex.objD K a :=
    CochainComplex.of_d (fun n ↦ K.obj ⦋n⦌) (AlternatingCofaceMapComplex.objD K) a
  rw [hL, hK]
  let c : (K.obj ⦋a⦌).X b ⟶ (L.obj ⦋a⦌).X (b + 1) :=
    schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS a b
  let c' : (K.obj ⦋a + 1⦌).X b ⟶ (L.obj ⦋a + 1⦌).X (b + 1) :=
    schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS (a + 1) b
  change c ≫ (∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • L.map (SimplexCategory.δ i)).f (b + 1) =
    (∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • K.map (SimplexCategory.δ i)).f b ≫ c'
  rw [cechCenter_sum_f, cechCenter_sum_f]
  simp only [HomologicalComplex.zsmul_f_apply, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z ↦ (-1 : ℤ) ^ (i : ℕ) • z)
    (schemePerfectCechTupleRightCenterForwardVertex_naturality f g F q hq U p hp hR hS
      (SimplexCategory.δ i) b)

end SerrePositivity.AlgebraicGeometry
