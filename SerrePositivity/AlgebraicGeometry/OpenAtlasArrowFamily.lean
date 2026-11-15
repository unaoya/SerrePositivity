module

public import SerrePositivity.AlgebraicGeometry.CartesianModelArrow
public import SerrePositivity.AlgebraicGeometry.OpenAtlasOriginalArrows

/-!
概要：対角の逆・反転・三重交叉の三種の射を、有限族の降下の具体的な入力にする。
方針：既存の比較・有限表示性・可換式の法則を、有限和の各成分へ入れる。
規約：元の環の Noether 性は要求しない。係数側の Noether 性で重なりの有限表示性を供給。
使われ方：G2 の三種の射の同じ段への同時降下。
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

/-- 三種の射の有限和の各成分の、既に構成した具体的な降下の入力。 -/
def atlasArrowFamily (e : I ⊕ ((I × I) ⊕ (I × I × I))) :
    CartesianModelArrow (Spec.map (CommRingCat.ofHom (algebraMap m.A R))) := by
  rcases e with i | (⟨i, a⟩ | ⟨i, a, b⟩)
  · exact {
      sourceModel := m.obj i
      source := U i
      targetModel := m.overlap i i
      sourceMap := m.map i
      targetMap := (m.overlap i i).ι ≫ m.map i
      comparison := m.comparison i
      base := j i ≫ f
      cartesian := m.cartesian i
      arrow := m.diagonalArrow i
      toBase := by simpa only [Category.assoc] using m.diagonalArrow_toBase i
      sourceQC := m.qc i
      sourceQS := m.qs i
      targetFP := (m.finitePresentation_overlap i i).1
    }
  · exact {
      sourceModel := m.overlap i a
      source := pullback (j i) (j a)
      targetModel := m.overlap a i
      sourceMap := (m.overlap i a).ι ≫ m.map i
      targetMap := (m.overlap a i).ι ≫ m.map a
      comparison := m.overlapComparison i a
      base := pullback.fst (j i) (j a) ≫ j i ≫ f
      cartesian := m.isPullback_overlapComparison_toBase i a
      arrow := m.reverseArrow i a
      toBase := by simpa only [Category.assoc] using m.reverseArrow_toBase i a
      sourceQC := (m.finitePresentation_overlap i a).2.1
      sourceQS := (m.finitePresentation_overlap i a).2.2
      targetFP := (m.finitePresentation_overlap a i).1
    }
  · exact {
      sourceModel := pullback (m.overlap i a).ι (m.overlap i b).ι
      source := pullback (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b))
      targetModel := m.overlap a b
      sourceMap := pullback.fst (m.overlap i a).ι (m.overlap i b).ι ≫
        (m.overlap i a).ι ≫ m.map i
      targetMap := (m.overlap a b).ι ≫ m.map a
      comparison := m.tripleComparison i a b
      base := pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b)) ≫
        pullback.fst (j i) (j a) ≫ j i ≫ f
      cartesian := m.isPullback_tripleComparison_toBase i a b
      arrow := m.tripleArrow i a b
      toBase := by simpa only [Category.assoc] using m.tripleArrow_toBase i a b
      sourceQC := (m.finitePresentation_triple i a b).2.1
      sourceQS := (m.finitePresentation_triple i a b).2.2
      targetFP := (m.finitePresentation_overlap a b).1
    }

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
