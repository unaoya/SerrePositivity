module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ShiftRepresentative

/-! 整数シフト代表の K(D) 同型を、実閉射と全 dg 自然な逆ホモトピーで回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (x : D) (n : ℤ) (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingShiftRepresentative R D x n)

/-- シフト代表同型の順射を持ち上げた、同じ実閉加群射。 -/
def dgGluingShiftRepresentativeHom :
    ((ForgetEnrichment.of (Complex R) (representable R x))⟦n⟧) ⟶
      ForgetEnrichment.of (Complex R) (representable R q.obj) :=
  (moduleToHomotopy R D).preimage q.comparison.hom

/-- 同じシフト代表同型の逆射を持ち上げた実閉加群射。 -/
def dgGluingShiftRepresentativeInv :
    ForgetEnrichment.of (Complex R) (representable R q.obj) ⟶
      ((ForgetEnrichment.of (Complex R) (representable R x))⟦n⟧) :=
  (moduleToHomotopy R D).preimage q.comparison.inv

lemma dgGluingShiftRepresentativeHom_map :
    (moduleToHomotopy R D).map (dgGluingShiftRepresentativeHom R D x n q) =
      q.comparison.hom := (moduleToHomotopy R D).map_preimage _

lemma dgGluingShiftRepresentativeInv_map :
    (moduleToHomotopy R D).map (dgGluingShiftRepresentativeInv R D x n q) =
      q.comparison.inv := (moduleToHomotopy R D).map_preimage _

/-- 同じ順・逆の合成は、全 dg 自然な加群ホモトピーで単位へ戻る。 -/
lemma dgGluingShiftRepresentativeHomInv_homotopy :
    Nonempty (ModuleHomotopy R D
      (dgGluingShiftRepresentativeHom R D x n q ≫ dgGluingShiftRepresentativeInv R D x n q)
      (𝟙 _)) := by
  apply (moduleToHomotopy_map_eq_iff R D _ _).1
  simp only [CategoryTheory.Functor.map_comp, dgGluingShiftRepresentativeHom_map,
    dgGluingShiftRepresentativeInv_map, Iso.hom_inv_id, CategoryTheory.Functor.map_id]

lemma dgGluingShiftRepresentativeInvHom_homotopy :
    Nonempty (ModuleHomotopy R D
      (dgGluingShiftRepresentativeInv R D x n q ≫ dgGluingShiftRepresentativeHom R D x n q)
      (𝟙 _)) := by
  apply (moduleToHomotopy_map_eq_iff R D _ _).1
  simp only [CategoryTheory.Functor.map_comp, dgGluingShiftRepresentativeHom_map,
    dgGluingShiftRepresentativeInv_map, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
