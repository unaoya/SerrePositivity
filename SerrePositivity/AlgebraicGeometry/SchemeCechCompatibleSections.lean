module

public import SerrePositivity.AlgebraicGeometry.SchemeCechSingletonSections

/-!
概要：全タプル Čech の equalizer の環を、被覆上の適合切断の環と同定する。
方針：二つの面を二重点への実際の制限と照合する。
規約：同型は成分ごとの切断環の演算を保つ。
使われ方：F7 の Čech H⁰ の有限環を大域切断と結ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace TopologicalSpace.Opens Opposite _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u}) {ι : Type} [DecidableEq ι]
variable (U : ι → Y.Opens) (φ : R →+* Γ(Y, ⊤))

/-- 長さ二の第零面は、第二の開集合から二重点への制限。 -/
theorem schemeCechSingletonSectionsEquiv_face_zero
    (a : FullRingCechCochains
      (algebraCechRingDiagram (schemeSectionAlgebraCechDiagram Y φ U)) 1) (t : Fin 2 → ι) :
    (Y.presheaf.map (eqToHom (cechOpenIntersection_tuple_two Y U t).symm).op).hom
        (fullAlgebraCechFace (schemeSectionAlgebraCechDiagram Y φ U) 0 a t) =
      (Y.presheaf.map (infLERight (U (t 0)) (U (t 1))).op).hom
        (schemeCechSingletonSectionsEquiv Y U φ a (t 1)) := by
  change (Y.presheaf.map _).hom ((Y.presheaf.map _).hom (a (t ∘ (0 : Fin 2).succAbove))) = _
  rw [← schemeCechSingletonSectionsEquiv_recover Y U φ a (t ∘ (0 : Fin 2).succAbove)]
  change (Y.presheaf.map _ ≫ Y.presheaf.map _ ≫ Y.presheaf.map _).hom
      (schemeCechSingletonSectionsEquiv Y U φ a (t 1)) = _
  rw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
  congr 2

/-- 長さ二の第一面は、第一の開集合から二重点への制限。 -/
theorem schemeCechSingletonSectionsEquiv_face_one
    (a : FullRingCechCochains
      (algebraCechRingDiagram (schemeSectionAlgebraCechDiagram Y φ U)) 1) (t : Fin 2 → ι) :
    (Y.presheaf.map (eqToHom (cechOpenIntersection_tuple_two Y U t).symm).op).hom
        (fullAlgebraCechFace (schemeSectionAlgebraCechDiagram Y φ U) 1 a t) =
      (Y.presheaf.map (infLELeft (U (t 0)) (U (t 1))).op).hom
        (schemeCechSingletonSectionsEquiv Y U φ a (t 0)) := by
  change (Y.presheaf.map _).hom ((Y.presheaf.map _).hom (a (t ∘ (1 : Fin 2).succAbove))) = _
  rw [← schemeCechSingletonSectionsEquiv_recover Y U φ a (t ∘ (1 : Fin 2).succAbove)]
  change (Y.presheaf.map _ ≫ Y.presheaf.map _ ≫ Y.presheaf.map _).hom
      (schemeCechSingletonSectionsEquiv Y U φ a (t 0)) = _
  rw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
  congr 2

/-- 二つの面の equalizer 条件は、層の二重点での適合条件と一致する。 -/
theorem schemeCechSingletonSectionsEquiv_mem_iff
    (a : FullRingCechCochains
      (algebraCechRingDiagram (schemeSectionAlgebraCechDiagram Y φ U)) 1) :
    a ∈ fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U) ↔
      schemeCechSingletonSectionsEquiv Y U φ a ∈ schemeCompatibleSections Y U := by
  constructor
  · intro ha i j
    have hh : fullAlgebraCechFace (schemeSectionAlgebraCechDiagram Y φ U) 0 a =
        fullAlgebraCechFace (schemeSectionAlgebraCechDiagram Y φ U) 1 a := ha
    let t : Fin 2 → ι := ![i, j]
    have he := congrArg (fun f ↦
      (Y.presheaf.map (eqToHom (cechOpenIntersection_tuple_two Y U t).symm).op).hom (f t)) hh
    rw [schemeCechSingletonSectionsEquiv_face_zero, schemeCechSingletonSectionsEquiv_face_one] at he
    exact he.symm
  · intro ha
    change fullAlgebraCechFace (schemeSectionAlgebraCechDiagram Y φ U) 0 a =
      fullAlgebraCechFace (schemeSectionAlgebraCechDiagram Y φ U) 1 a
    funext t
    apply ((ConcreteCategory.isIso_iff_bijective
      (Y.presheaf.map (eqToHom (cechOpenIntersection_tuple_two Y U t).symm).op)).mp
        inferInstance).1
    change (Y.presheaf.map _).hom
        (fullAlgebraCechFace (schemeSectionAlgebraCechDiagram Y φ U) 0 a t) =
      (Y.presheaf.map _).hom
        (fullAlgebraCechFace (schemeSectionAlgebraCechDiagram Y φ U) 1 a t)
    rw [schemeCechSingletonSectionsEquiv_face_zero, schemeCechSingletonSectionsEquiv_face_one]
    exact (ha (t 0) (t 1)).symm

/-- Čech H⁰ に用いる適合切断の部分代数と、層の適合切断の部分環との環の同型。 -/
def schemeCechCompatibleSectionsEquiv :
    fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U) ≃+*
      schemeCompatibleSections Y U where
  toFun a := ⟨schemeCechSingletonSectionsEquiv Y U φ a.val,
    (schemeCechSingletonSectionsEquiv_mem_iff Y U φ a.val).mp a.property⟩
  invFun a := ⟨(schemeCechSingletonSectionsEquiv Y U φ).symm a.val,
    (schemeCechSingletonSectionsEquiv_mem_iff Y U φ _).mpr (by
      simpa only [RingEquiv.apply_symm_apply] using a.property)⟩
  left_inv a := Subtype.ext ((schemeCechSingletonSectionsEquiv Y U φ).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((schemeCechSingletonSectionsEquiv Y U φ).apply_symm_apply a.val)
  map_mul' a b := Subtype.ext ((schemeCechSingletonSectionsEquiv Y U φ).map_mul a.val b.val)
  map_add' a b := Subtype.ext ((schemeCechSingletonSectionsEquiv Y U φ).map_add a.val b.val)

end SerrePositivity.AlgebraicGeometry
