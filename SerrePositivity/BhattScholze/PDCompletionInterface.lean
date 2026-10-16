module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarRestriction

/-! # 実際の導来(p,d)完備化H⁰のBS側の作用の接続

受領したF3の対象・環構造・標準射をそのまま使う。
H⁰自身と試験環自身の作用に関する導来完備性を既存係数制限で接続する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable (A : Type u) [CommRing A] (p : ℕ) (d : A)

/-- 実H⁰は自身の作用についてp導来完備。標準射からの作用と既存比較で接続する。 -/
theorem pdCompletionH0_self_complete_p :
    letI := pdCompletionCommRing A p d
    IsModuleComplete (PDCompletionH0 A p d) (p : PDCompletionH0 A p d)
      (ModuleCat.of (PDCompletionH0 A p d) (PDCompletionH0 A p d)) := by
  let := pdCompletionCommRing A p d
  let := (pdCompletionUnit A p d).toAlgebra
  let : Module A (PDCompletionH0 A p d) := (pdCompletionUnit A p d).toAlgebra.toModule
  simpa only [map_natCast] using
    (isModuleComplete_algebraMap_iff A (PDCompletionH0 A p d) (p : A)
      (PDCompletionH0 A p d)).mpr (pdCompletionH0_isComplete_p A p d)

/-- 実H⁰は自身の作用について標準像j(d)導来完備。 -/
theorem pdCompletionH0_self_complete_d :
    letI := pdCompletionCommRing A p d
    IsModuleComplete (PDCompletionH0 A p d) (pdCompletionUnit A p d d)
      (ModuleCat.of (PDCompletionH0 A p d) (PDCompletionH0 A p d)) := by
  let := pdCompletionCommRing A p d
  let := (pdCompletionUnit A p d).toAlgebra
  let : Module A (PDCompletionH0 A p d) := (pdCompletionUnit A p d).toAlgebra.toModule
  exact (isModuleComplete_algebraMap_iff A (PDCompletionH0 A p d) d
    (PDCompletionH0 A p d)).mpr (pdCompletionH0_isComplete_d A p d)

/-- 試験環自身のp,g(d)導来完備性から、実H⁰の環としての一意延長を得る。 -/
theorem existsUnique_pdCompletionRingHom (T : Type u) [CommRing T] (g : A →+* T)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    ∃! h : PDCompletionH0 A p d →+* T, h.comp (pdCompletionUnit A p d) = g := by
  let := g.toAlgebra
  apply pdCompletion_existsUnique_ringHom A p d T g
  · apply (isModuleComplete_algebraMap_iff A T (p : A) T).mp
    simpa only [map_natCast] using hp
  · exact (isModuleComplete_algebraMap_iff A T d T).mp hd

/-- 実H⁰からの環射は、標準基底射との合成によって決まる。 -/
theorem pdCompletionRingHom_ext (T : Type u) [CommRing T]
    (g : A →+* T) (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    ∀ f h : PDCompletionH0 A p d →+* T,
      f.comp (pdCompletionUnit A p d) = g →
      h.comp (pdCompletionUnit A p d) = g → f = h := by
  let := pdCompletionCommRing A p d
  obtain ⟨k, _, hu⟩ := existsUnique_pdCompletionRingHom A p d T g hp hd
  intro f h hf hh
  exact (hu f hf).trans (hu h hh).symm

end SerrePositivity.BhattScholze
