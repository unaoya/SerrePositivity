module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasTripleModels

/-!
概要：元の対角の逆・反転・三重交叉の射を、固定した模型への射として明示する。
方針：元のファイバー積の対角・反転・lift と、既存の重なりの比較を合成する。
規約：同じ係数基底上の可換式を保持する。
使われ方：G2 の三種の有限個の射を同じ係数段へ降ろす入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {k : Type v} [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
  {I : Type u} {X : Scheme.{u}} {U : I → Scheme.{u}} {j : ∀ i, U i ⟶ X}
  [∀ i, IsOpenImmersion (j i)] {f : X ⟶ Spec (CommRingCat.of R)}
  (m : OpenAtlasModelData k U j f)

/-- 元の対角の逆を、固定した重なりの模型への射として取る。 -/
def diagonalArrow (i : I) : U i ⟶ m.overlap i i :=
  pullback.lift (𝟙 (U i)) (𝟙 (U i)) (by simp) ≫ m.overlapComparison i i

/-- 元の対角の射は、同じ係数基底上の射。 -/
theorem diagonalArrow_toBase (i : I) :
    m.diagonalArrow i ≫ (m.overlap i i).ι ≫ m.map i =
      j i ≫ f ≫ Spec.map (CommRingCat.ofHom (algebraMap m.A R)) := by
  calc
    _ = m.comparison i ≫ m.map i := by
      simp only [diagonalArrow, Category.assoc, (m.isPullback_overlapComparison i i).w_assoc,
        pullback.lift_fst_assoc, Category.id_comp]
    _ = _ := by simpa only [Category.assoc] using (m.cartesian i).w

/-- 元の二重交叉の反転を、固定した逆向きの重なりの模型への射として取る。 -/
def reverseArrow (i a : I) : pullback (j i) (j a) ⟶ m.overlap a i :=
  (pullbackSymmetry (j i) (j a)).hom ≫ m.overlapComparison a i

/-- 元の反転の射は、同じ係数基底上の射。 -/
theorem reverseArrow_toBase (i a : I) :
    m.reverseArrow i a ≫ (m.overlap a i).ι ≫ m.map a =
      pullback.fst (j i) (j a) ≫ j i ≫ f ≫
        Spec.map (CommRingCat.ofHom (algebraMap m.A R)) := by
  simp only [reverseArrow, Category.assoc, (m.isPullback_overlapComparison_toBase a i).w,
    pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc, pullback.condition_assoc]

/-- 元の三重交叉から次の二重交叉への実際の射。 -/
def tripleNextPair (i a b : I) :
    pullback (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b)) ⟶ pullback (j a) (j b) := by
  refine pullback.lift
    (pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b)) ≫ pullback.snd (j i) (j a))
    (pullback.snd (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b)) ≫ pullback.snd (j i) (j b)) ?_
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
    pullback.condition, ← Category.assoc]

/-- 元の三重交叉の射を、固定した次の重なりの模型への射として取る。 -/
def tripleArrow (i a b : I) :
    pullback (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b)) ⟶ m.overlap a b :=
  tripleNextPair (j := j) i a b ≫ m.overlapComparison a b

/-- 元の三重交叉の射は、同じ係数基底上の射。 -/
theorem tripleArrow_toBase (i a b : I) :
    m.tripleArrow i a b ≫ (m.overlap a b).ι ≫ m.map a =
      pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b)) ≫
        pullback.fst (j i) (j a) ≫ j i ≫ f ≫
        Spec.map (CommRingCat.ofHom (algebraMap m.A R)) := by
  simp only [tripleArrow, tripleNextPair, Category.assoc,
    (m.isPullback_overlapComparison_toBase a b).w, pullback.lift_fst_assoc]
  rw [← pullback.condition_assoc]

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
