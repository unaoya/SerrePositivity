module

public import SerrePositivity.AlgebraicGeometry.AffineFppfCompositeTupleTotal
public import SerrePositivity.AlgebraicGeometry.AffineScalarPerfectTupleTotal
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalBaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：相対アフィンfppfと固有全射の合成に、全ての試験基底でのČech降下性を供給する。
方針：同じ反復pullbackでF11を適用し、元のアフィンΓの比較で任意の被覆へ戻す。
規約：基底も元の合成も変えず、Γの完全性と同じタプルtotalの比較だけを使う。
使われ方：Noether閉像帰納とRydh細分の消去（承認済み計画D07）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 相対アフィンfppfと元の固有全射の合成は、同じ普遍Čech降下性を持つ。 -/
theorem perfectCechUniversalDescent_affine_fppf_comp
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A B : Scheme.{u}} [IsAffine A] (q : A ⟶ B)
    [IsAffineHom q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (g : B ⟶ Spec (CommRingCat.of R)) [IsProper g] [Surjective g]
    (p : ℕ) (hp : p.Prime) (hg : PerfectCechUniversalDescent p hp g) :
    PerfectCechUniversalDescent p hp (q ≫ g) := by
  intro T _ _ hT t ι _ _ U hU hcU
  let AT := pullback (q ≫ g) t
  let gT := pullback.snd g t
  let E := pullbackRightPullbackFstIso g t q
  let qT := E.inv ≫ pullback.snd q (pullback.fst g t)
  haveI : IsAffine AT := inferInstance
  haveI : IsAffineHom (pullback.snd q (pullback.fst g t)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback q (pullback.fst g t))
      (inferInstance : IsAffineHom q)
  haveI : IsAffineHom qT := by dsimp only [qT]; infer_instance
  haveI : Flat qT := by dsimp only [qT]; infer_instance
  haveI : Surjective qT := by dsimp only [qT]; infer_instance
  haveI : LocallyOfFinitePresentation qT := by dsimp only [qT]; infer_instance
  have hcomp : qT ≫ gT = pullback.snd (q ≫ g) t := by
    simpa only [qT, gT, E, Category.assoc] using
      (pullbackRightPullbackFstIso_inv_snd_snd g t q)
  have hgT := perfectCechUniversalDescent_baseChange p hp g t hg
  have hPC := affine_fppf_composite_tupleTotal_acyclic qT gT p hp hT hgT
  rw [hcomp] at hPC
  have hUnit (i : Unit) : IsAffineOpen (⊤ : AT.Opens) := isAffineOpen_top _
  have hcUnit : (⨆ _ : Unit, (⊤ : AT.Opens)) = ⊤ := by simp
  have hx := (affineScalarPerfectCech_exact_iff_tuple_total_acyclic AT
    (pullback.snd (q ≫ g) t) p hp hT (fun _ : Unit ↦ ⊤) hUnit hcUnit).mpr hPC
  exact (affineScalarPerfectCech_exact_iff_tuple_total_acyclic AT
    (pullback.snd (q ≫ g) t) p hp hT U hU hcU).mp hx

end SerrePositivity.AlgebraicGeometry
