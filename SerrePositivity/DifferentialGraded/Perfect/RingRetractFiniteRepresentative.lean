module
public import SerrePositivity.DifferentialGraded.Perfect.RingTriangleFiniteModel

/-! # 有限射影複体の導来retractの有限射影代表

次数幅の帰納法。上端被覆で短い幅へ帰着し、逆回転三角形のconeで元の対象へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedRetract_finiteRange (width : ℕ) (a : ℤ)
    (P : Complex A) (hP : strictlyPerfectComplex A P)
    (hge : P.IsStrictlyGE a) (hle : P.IsStrictlyLE (a + (width : ℤ)))
    {X : DerivedCategory (ModuleCat.{u} A)} (r : Retract X (DerivedCategory.Q.obj P)) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧ K.IsStrictlyGE a ∧
      K.IsStrictlyLE (a + (width : ℤ)) ∧ Nonempty (DerivedCategory.Q.obj K ≅ X) := by
  induction width generalizing a P X with
  | zero =>
    let := hge
    have : P.IsStrictlyLE a := by simpa only [Nat.cast_zero, add_zero] using hle
    simpa only [Nat.cast_zero, add_zero] using ringDerivedRetract_pure_finiteRange A P hP a r
  | succ width ih =>
    let b := a + (width : ℤ) + 1
    have hbound : a + (width.succ : ℤ) = b := by dsimp only [b]; omega
    let := hge
    have : P.IsStrictlyLE b := by simpa only [hbound] using hle
    have hab : a < b := by dsimp only [b]; omega
    obtain ⟨F, hf, hp, T, hT, h₁, h₂, P', hP', hge', hle', ⟨r'⟩⟩ :=
      ringDerivedRetract_reduce_range A P hP a b r hab
    have hb : b - 1 = a + (width : ℤ) := by dsimp only [b]; omega
    have hleW : P'.IsStrictlyLE (a + (width : ℤ)) := by simpa only [hb] using hle'
    obtain ⟨K, hK, hgeK, hleK, ⟨eK⟩⟩ := ih a P' hP' hge' hleW r'
    let := hf
    let := hp
    let := hgeK
    have : K.IsStrictlyLE (b - 1) := by simpa only [hb] using hleK
    obtain ⟨L, hL, hgeL, hleL, ⟨eL⟩⟩ := ringDerivedTriangle_middle_finiteRange A T hT F K hK
      a b hab.le (eqToIso h₁).symm eK
    refine ⟨L, hL, hgeL, ?_, ⟨eL ≪≫ eqToIso h₂⟩⟩
    simpa only [hbound] using hleL

lemma ringDerivedRetract_finiteProjective (P : Complex A) (hP : strictlyPerfectComplex A P)
    {X : DerivedCategory (ModuleCat.{u} A)} (r : Retract X (DerivedCategory.Q.obj P)) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧ Nonempty (DerivedCategory.Q.obj K ≅ X) := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := ha
  let := hb
  let width := (b - a).toNat
  have hle : P.IsStrictlyLE (a + (width : ℤ)) :=
    P.isStrictlyLE_of_le b _ (by dsimp only [width]; omega)
  obtain ⟨K, hK, _, _, e⟩ := ringDerivedRetract_finiteRange A width a P hP ha hle r
  exact ⟨K, hK, e⟩

end SerrePositivity.DifferentialGraded
