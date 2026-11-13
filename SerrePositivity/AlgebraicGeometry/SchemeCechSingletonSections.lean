module

public import SerrePositivity.AlgebraicGeometry.SchemeCompatibleSections

/-!
概要：全タプル Čech の長さ一の切断族を、被覆の各開集合の切断族と比較する。
方針：長さ一の有限交叉と元の開集合の等式に沿う構造層の制限を使う。
規約：積と加法は実際の切断環の演算を保つ。
使われ方：F7 の適合切断の equalizer と層の貼り合わせの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable (Y : Scheme.{u}) {ι : Type} [DecidableEq ι] (U : ι → Y.Opens)

/-- タプルの台による有限交叉は、タプルの各位置での交叉に一致する。 -/
theorem cechOpenIntersection_tuple {k : ℕ} (t : Fin k → ι) :
    cechOpenIntersection U (cechTupleSupport t) = ⨅ j, U (t j) := by
  unfold cechOpenIntersection
  apply le_antisymm
  · apply le_iInf
    intro j
    exact iInf_le_of_le (t j) (iInf_le_of_le
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) le_rfl)
  · apply le_iInf
    intro i
    apply le_iInf
    intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact iInf_le _ j

/-- 長さ一のタプルの交叉は、その一つの開集合。 -/
theorem cechOpenIntersection_tuple_one (t : Fin 1 → ι) :
    cechOpenIntersection U (cechTupleSupport t) = U (t 0) := by
  rw [cechOpenIntersection_tuple]
  simp

/-- 長さ二のタプルの交叉は、その二つの開集合の交叉。 -/
theorem cechOpenIntersection_tuple_two (t : Fin 2 → ι) :
    cechOpenIntersection U (cechTupleSupport t) = U (t 0) ⊓ U (t 1) := by
  rw [cechOpenIntersection_tuple]
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · apply le_iInf
    intro j
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right

variable {R : Type u} [CommRing R] (φ : R →+* Γ(Y, ⊤))

/-- 長さ一の Čech 切断族と、元の被覆上の切断族との環の同型。 -/
def schemeCechSingletonSectionsEquiv :
    FullRingCechCochains (algebraCechRingDiagram (schemeSectionAlgebraCechDiagram Y φ U)) 1 ≃+*
      ((i : ι) → Γ(Y, U i)) where
  toFun a i := (Y.presheaf.map (eqToHom
    (cechOpenIntersection_tuple_one Y U (fun _ ↦ i)).symm).op).hom (a (fun _ ↦ i))
  invFun a t := (Y.presheaf.map (eqToHom (cechOpenIntersection_tuple_one Y U t)).op).hom
    (a (t 0))
  left_inv a := by
    funext t
    obtain ⟨i, rfl⟩ : ∃ i, t = fun _ ↦ i :=
      ⟨t 0, funext (fun j ↦ congrArg t (Subsingleton.elim j 0))⟩
    change (Y.presheaf.map _).hom ((Y.presheaf.map _).hom (a (fun _ ↦ i))) = _
    change (Y.presheaf.map _ ≫ Y.presheaf.map _).hom (a (fun _ ↦ i)) = _
    rw [← Y.presheaf.map_comp]
    change (Y.presheaf.map (𝟙 _)).hom (a (fun _ ↦ i)) = _
    rw [Y.presheaf.map_id]
    rfl
  right_inv a := by
    funext i
    change (Y.presheaf.map _).hom ((Y.presheaf.map _).hom (a i)) = _
    change (Y.presheaf.map _ ≫ Y.presheaf.map _).hom (a i) = _
    rw [← Y.presheaf.map_comp]
    change (Y.presheaf.map (𝟙 _)).hom (a i) = _
    rw [Y.presheaf.map_id]
    rfl
  map_mul' a b := by funext i; exact map_mul _ _ _
  map_add' a b := by funext i; exact map_add _ _ _

/-- 元のタプルの切断は、被覆上の切断を長さ一の交叉へ制限して戻せる。 -/
theorem schemeCechSingletonSectionsEquiv_recover
    (a : FullRingCechCochains
      (algebraCechRingDiagram (schemeSectionAlgebraCechDiagram Y φ U)) 1) (t : Fin 1 → ι) :
    (Y.presheaf.map (eqToHom (cechOpenIntersection_tuple_one Y U t)).op).hom
        (schemeCechSingletonSectionsEquiv Y U φ a (t 0)) = a t :=
  congrFun ((schemeCechSingletonSectionsEquiv Y U φ).symm_apply_apply a) t

end SerrePositivity.AlgebraicGeometry
