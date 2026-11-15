module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasReverseNaturality

/-!
概要：元の対角の自然性から、有限段の対角の逆の二側の式を極限上で供給する。
方針：比較の二射影と元の開包含の mono 性を使う。
規約：有限段そのものの逆の式は、後の共通段へ移す一致判定で供給する。
使われ方：G2 の gluing datum の対角の同型性の入力。
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

/-- 元の開チャートの実際の対角。 -/
def originalDiagonal (i : I) : U i ⟶ pullback (j i) (j i) :=
  pullback.lift (𝟙 _) (𝟙 _) (by simp)

/-- 元の対角と第一射影は二側の逆。 -/
theorem originalDiagonal_fst_inverse (i : I) :
    originalDiagonal (j := j) i ≫ pullback.fst (j i) (j i) = 𝟙 _ ∧
      pullback.fst (j i) (j i) ≫ originalDiagonal (j := j) i = 𝟙 _ := by
  constructor
  · simp [originalDiagonal]
  · have he : pullback.fst (j i) (j i) = pullback.snd (j i) (j i) :=
      (cancel_mono (j i)).mp pullback.condition
    apply pullback.hom_ext <;> simp [originalDiagonal, Category.assoc, he]

variable (l : ∀ e, pullback γ (m.atlasArrowFamily e).sourceMap ⟶
    pullback γ (m.atlasArrowFamily e).targetMap)
  (hl : ∀ e, l e ≫ pullback.fst γ (m.atlasArrowFamily e).targetMap =
    pullback.fst γ (m.atlasArrowFamily e).sourceMap)
  (hn : ∀ e, (m.atlasArrowFamily e).comparisonAt b γ h ≫ l e ≫
    pullback.snd γ (m.atlasArrowFamily e).targetMap = (m.atlasArrowFamily e).arrow)
include hl hn

/-- 元の対角と段の対角の候補は実際の段の標的への射として可換。 -/
theorem stageDiagonal_naturality (i : I) :
    (m.atlasArrowFamily (.inl i)).comparisonAt b γ h ≫ m.stageDiagonal γ l i =
      originalDiagonal (j := j) i ≫ m.pairComparisonAt b γ h i i := by
  apply pullback.hom_ext
  · rw [Category.assoc, m.stageDiagonal_toBase γ l hl i]
    simp only [pairComparisonAt, CartesianModelArrow.comparisonAt, atlasArrowFamily,
      originalDiagonal, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.id_comp]
  · simpa only [pairComparisonAt, stageDiagonal, atlasArrowFamily, CartesianModelArrow.comparisonAt,
      diagonalArrow, originalDiagonal, Category.assoc, pullback.lift_snd] using hn (.inl i)

/-- 元のチャートの比較の後では、段の対角の候補と開包含の合成は恒等射。 -/
theorem stageDiagonal_right_inverse_after_comparison (i : I) :
    (m.atlasArrowFamily (.inl i)).comparisonAt b γ h ≫ m.stageDiagonal γ l i ≫
        baseChangedOverlapMap γ (m.map i) (m.overlap i i).ι =
      (m.atlasArrowFamily (.inl i)).comparisonAt b γ h := by
  rw [← Category.assoc, m.stageDiagonal_naturality b γ h l hl hn i, Category.assoc,
    m.pairComparisonAt_toChart b γ h i i]
  simp [originalDiagonal]

/-- 元の重なりの比較の後では、段の開包含と対角の候補の合成も恒等射。 -/
theorem stageDiagonal_left_inverse_after_comparison (i : I) :
    m.pairComparisonAt b γ h i i ≫ baseChangedOverlapMap γ (m.map i) (m.overlap i i).ι ≫
        m.stageDiagonal γ l i = m.pairComparisonAt b γ h i i := by
  rw [← Category.assoc, m.pairComparisonAt_toChart b γ h i i, Category.assoc,
    m.stageDiagonal_naturality b γ h l hl hn i, ← Category.assoc,
    (originalDiagonal_fst_inverse (j := j) i).2, Category.id_comp]

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
