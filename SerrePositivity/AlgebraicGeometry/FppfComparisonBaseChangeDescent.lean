module

public import SerrePositivity.AlgebraicGeometry.FppfComparisonRefiner
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalAffineRefinement

/-!
概要：元のnerveへの細分射で、相対fppfの合成の底変換の普遍Čech降下を得る。
方針：元のfppf射の第一座標に沿う底変換へ平坦降下を使い、D06で細分を消去する。
規約：非平坦な合成q≫g自体を平坦と仮定しない。
使われ方：相対fppfの正次数の軸比較（承認済み計画F10）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 同じfppf細分の合成が平坦な底変換であることから、元の底変換の降下を得る。 -/
theorem fppfComparison_baseChange_descent
    {R : Type u} [CommRing R] {A B : Scheme.{u}} [IsAffine A]
    (q : A ⟶ B) [IsAffineHom q] [Flat q] [Surjective q]
    [LocallyOfFinitePresentation q]
    (g : B ⟶ Spec (CommRingCat.of R)) [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g] (n : SimplexCategory)
    (p : ℕ) (hp : p.Prime) : PerfectCechUniversalDescent p hp
      (pullback.snd (q ≫ g) (augmentedNerveBase g (.of n))) := by
  let f := pullback.snd (q ≫ g) (augmentedNerveBase g (.of n))
  let a := fppfComparisonRefiner q g n
  have hcomp : a ≫ f = pullback.snd q (WidePullback.π (fun _ : Fin (n.len+1) ↦ g) 0) :=
    fppfComparisonRefiner_over q g n
  haveI : IsAffineHom (pullback.snd q (WidePullback.π (fun _ : Fin (n.len+1) ↦ g) 0)) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback q (WidePullback.π (fun _ : Fin (n.len+1) ↦ g) 0))
      (inferInstance : IsAffineHom q)
  haveI : IsAffineHom (a ≫ f) := by rw [hcomp]; infer_instance
  haveI : LocallyOfFinitePresentation (a ≫ f) := by rw [hcomp]; infer_instance
  apply perfectCechUniversalDescent_of_affine_refinement p hp f a
  rw [hcomp]
  exact perfectCechUniversalDescent_flat_surjective p hp _

end SerrePositivity.AlgebraicGeometry
