module

public import SerrePositivity.AlgebraicGeometry.CenterComplementLocalization
public import SerrePositivity.AlgebraicGeometry.SchemeCechScalarTensorSurjective
public import SerrePositivity.AlgebraicGeometry.TensorCokernelVanishing
public import Mathlib.RingTheory.Flat.Localization

/-!
概要：中心外で同型な射の切断部分代数のスカラー余核は、中心内に台を持つ。
方針：各素点への局所化で実際の構造射が同型となることを使う。
規約：スカラー写像は基底環から適合する切断への実際の写像。
使われ方：有限性と合わせて次数零の余核を中心の冪で消す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
variable [IsIso (f ∣_ affineCenterComplement I)]
variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤)


include hU hcU in
/-- 中心外で同型な射の切断代数のスカラー余核の台は中心内。
BST13 Lemma 3.9 の次数零で使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeCechScalarCokernel_support_subset_of_isoOffCenter :
    Module.support R ((fullAlgebraCechEqualizer
      (schemeSectionAlgebraCechDiagram X (schemeScalarHom X f) U)) ⧸
        LinearMap.range (Algebra.linearMap R (fullAlgebraCechEqualizer
          (schemeSectionAlgebraCechDiagram X (schemeScalarHom X f) U)))) ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  apply cokernel_support_subset_of_localizedTensor_surjective
  intro P hP
  let A := Localization P.asIdeal.primeCompl
  let g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  let iY := pullback.snd f g
  let j := pullback.fst f g
  letI : IsIso iY := pullback_localization_isIso_of_centerComplement f I P hP
  letI : IsAffineHom j := MorphismProperty.pullback_fst f g
    (inferInstance : IsAffineHom g)
  letI : Module.Flat R A := IsLocalization.flat A P.asIdeal.primeCompl
  exact schemeCechScalarTensor_surjective f iY j (IsPullback.of_hasPullback f g) U hU
    (fun i ↦ (hU i).preimage j) (j.iSup_preimage_eq_top hcU)

end SerrePositivity.AlgebraicGeometry
