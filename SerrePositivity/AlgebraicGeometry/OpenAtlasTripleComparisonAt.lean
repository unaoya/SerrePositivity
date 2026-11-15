module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasReverseNaturality

/-!
概要：元の三重交叉と段の実際の三重交叉の比較を、固定模型の底変換の比較につなぐ。
方針：二重交叉の比較を pullback lift し、具体的な同型との合成を二射影で確認する。
規約：元の三重交叉を保持し、係数射の単射性は仮定しない。
使われ方：G2 の L の自然性と cocycle の極限での照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {k : Type v} [CommRing k] [IsNoetherianRing k]
  {R : Type u} [CommRing R] [Algebra k R]
  {I : Type u} {X : Scheme.{u}} {U : I → Scheme.{u}} {j : ∀ i, U i ⟶ X}
  [∀ i, IsOpenImmersion (j i)] {f : X ⟶ Spec (CommRingCat.of R)}
  (m : OpenAtlasModelData k U j f)
  {B : Scheme.{u}} (b : Spec (CommRingCat.of R) ⟶ B)
  (γ : B ⟶ Spec (CommRingCat.of m.A))
  (h : b ≫ γ = Spec.map (CommRingCat.ofHom (algebraMap m.A R)))

/-- 元の三重交叉から段の重なりの実際の交叉への比較。 -/
def tripleComparisonAt (i a c : I) :
    pullback (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ⟶
      pullback (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) := by
  refine pullback.lift
    (pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
      m.pairComparisonAt b γ h i a)
    (pullback.snd (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
      m.pairComparisonAt b γ h i c) ?_
  rw [Category.assoc, m.pairComparisonAt_toChart b γ h i a,
    Category.assoc, m.pairComparisonAt_toChart b γ h i c,
    ← Category.assoc, pullback.condition, Category.assoc]

/-- 実際の三重交叉の比較の第一射影。 -/
@[reassoc (attr := simp)] theorem tripleComparisonAt_fst (i a c : I) :
    m.tripleComparisonAt b γ h i a c ≫
      pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) =
      pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
        m.pairComparisonAt b γ h i a := by simp [tripleComparisonAt]

/-- 実際の三重交叉の比較の第二射影。 -/
@[reassoc (attr := simp)] theorem tripleComparisonAt_snd (i a c : I) :
    m.tripleComparisonAt b γ h i a c ≫
      pullback.snd (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (baseChangedOverlapMap γ (m.map i) (m.overlap i c).ι) =
      pullback.snd (pullback.fst (j i) (j a)) (pullback.fst (j i) (j c)) ≫
        m.pairComparisonAt b γ h i c := by simp [tripleComparisonAt]

/-- 段の実際の交叉との比較を、固定した三重交叉模型の底変換との比較へ移す式。 -/
theorem tripleComparisonAt_iso (i a c : I) :
    m.tripleComparisonAt b γ h i a c ≫
        (baseChangedOverlapTripleIso γ (m.map i) (m.overlap i a).ι (m.overlap i c).ι).hom =
      (m.atlasArrowFamily (.inr (.inr (i, a, c)))).comparisonAt b γ h := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangedOverlapTripleIso_hom_fst]
    simp [tripleComparisonAt, pairComparisonAt, CartesianModelArrow.comparisonAt,
      atlasArrowFamily, Category.assoc]
  · simp only [Category.assoc, baseChangedOverlapTripleIso_hom_snd,
      CartesianModelArrow.comparisonAt, atlasArrowFamily, pullback.lift_snd]
    apply pullback.hom_ext <;>
      simp [tripleComparisonAt, baseChangedOverlapTripleComparison, cartesianPullbackMap,
        pairComparisonAt, CartesianModelArrow.comparisonAt, atlasArrowFamily, tripleComparison,
        Category.assoc]

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
