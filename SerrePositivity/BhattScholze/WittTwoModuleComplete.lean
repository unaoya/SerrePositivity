module

public import SerrePositivity.BhattScholze.WittTwoModuleSequence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarRestriction

/-! # W₂へのδ基底作用に関する実導来完備性

具体的な第0成分の核を使い、終域のf(r),f(φ(r))完備性からW₂のr完備性を得る。
(p,d)への適用ではφ(d)完備性を別途供給する必要がある。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]

/-- 第0座標の核は、φによる作用についての終域の実導来完備性を反映する。 -/
theorem wittTwoKernel_isModuleComplete (D : DeltaStructure p A) (f : A →+* B) (r : A)
    (hr : IsModuleComplete B (f (D.frobeniusLift r)) (ModuleCat.of B B)) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    IsModuleComplete A r (ModuleCat.of A (wittTwoProjectionLinear D f).ker) := by
  let := f.toAlgebra
  let := (wittTwoBaseMap D f).toAlgebra
  let K := (wittTwoProjectionLinear D f).ker
  let E : (ℕ → K) ≃ (ℕ → B) := Equiv.piCongrRight (fun _ ↦ (wittTwoKernelEquiv D f).toEquiv)
  have he (x : ℕ → K) : E (adicRecurrenceMap r x) =
      adicRecurrenceMap (f (D.frobeniusLift r)) (E x) := by
    funext n
    change wittTwoKernelEquiv D f (x n - r • x (n + 1)) =
      wittTwoKernelEquiv D f (x n) - f (D.frobeniusLift r) * wittTwoKernelEquiv D f (x (n + 1))
    rw [map_sub, wittTwoKernelEquiv_smul]
  have hb := (isModuleComplete_iff_recurrence_bijective B (f (D.frobeniusLift r)) _).mp hr
  apply (isModuleComplete_iff_recurrence_bijective A r _).mpr
  constructor
  · intro x y hxy
    apply E.injective
    apply hb.injective
    rw [← he, ← he, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hb.surjective (E y)
    refine ⟨E.symm z, E.injective ?_⟩
    rw [he, E.apply_symm_apply, hz]

/-- 第0座標線形射は全射。終域の各元に座標(b,0)を選ぶ。 -/
theorem wittTwoProjectionLinear_surjective (D : DeltaStructure p A) (f : A →+* B) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    Function.Surjective (wittTwoProjectionLinear D f) := by
  let := f.toAlgebra
  let := (wittTwoBaseMap D f).toAlgebra
  intro b
  exact ⟨TruncatedWittVector.mk p (fun i ↦ if i = 0 then b else 0), rfl⟩

/-- δ基底作用によるW₂は、f(r)とf(φ(r))で完備な終域の拡大としてr導来完備。 -/
theorem wittTwo_isModuleComplete (D : DeltaStructure p A) (f : A →+* B) (r : A)
    (hr : IsModuleComplete B (f r) (ModuleCat.of B B))
    (hφ : IsModuleComplete B (f (D.frobeniusLift r)) (ModuleCat.of B B)) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    IsModuleComplete A r (ModuleCat.of A (WittTwo p B)) := by
  let := f.toAlgebra
  let := (wittTwoBaseMap D f).toAlgebra
  let S := (wittTwoProjectionLinear D f).shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer
    (wittTwoProjectionLinear_surjective D f)
  have hk := wittTwoKernel_isModuleComplete D f r hφ
  have hb : IsModuleComplete A r (ModuleCat.of A B) :=
    (isModuleComplete_algebraMap_iff A B r B).mp hr
  exact isModuleComplete_extension A r S hS hk hb

/-- p座標のW₂完備性には、終域のp完備性だけで十分。φ(p)=pを使う。 -/
theorem wittTwo_isModuleComplete_p (D : DeltaStructure p A) (f : A →+* B)
    (hp : IsModuleComplete B (p : B) (ModuleCat.of B B)) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    IsModuleComplete A (p : A) (ModuleCat.of A (WittTwo p B)) := by
  apply wittTwo_isModuleComplete D f (p : A)
  · simpa only [map_natCast] using hp
  · simpa only [map_natCast] using hp

end SerrePositivity.BhattScholze
