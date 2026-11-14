module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulated

/-! 前三角性から cone の K(D) での代表を選び、実閉射と全 dg 自然な逆ホモトピーを回収する。 -/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (x y : D)
  (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶
    ForgetEnrichment.of (Complex R) (representable R y))
structure DGGluingConeRepresentative where
  obj : D
  comparison :
    (moduleToHomotopy R D).obj (moduleCone R D f) ≅
      (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R) (representable R obj))

lemma dgGluingConeRepresentative_nonempty (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    Nonempty (DGGluingConeRepresentative R D x y f) := by
  let := hD
  have hcone := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_cone R D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R D) f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable_representable R D x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable_representable R D y)
  obtain ⟨z, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R D _).1 hcone
  exact ⟨⟨z, e⟩⟩

def dgGluingChooseConeRepresentative (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    DGGluingConeRepresentative R D x y f :=
  Classical.choice (dgGluingConeRepresentative_nonempty R D x y f hD)

variable (q : DGGluingConeRepresentative R D x y f)
def dgGluingConeRepresentativeHom :
    moduleCone R D f ⟶ ForgetEnrichment.of (Complex R) (representable R q.obj) :=
  (moduleToHomotopy R D).preimage q.comparison.hom

def dgGluingConeRepresentativeInv :
    ForgetEnrichment.of (Complex R) (representable R q.obj) ⟶ moduleCone R D f :=
  (moduleToHomotopy R D).preimage q.comparison.inv

lemma dgGluingConeRepresentativeHom_map :
    (moduleToHomotopy R D).map (dgGluingConeRepresentativeHom R D x y f q) = q.comparison.hom :=
  (moduleToHomotopy R D).map_preimage _
lemma dgGluingConeRepresentativeInv_map :
    (moduleToHomotopy R D).map (dgGluingConeRepresentativeInv R D x y f q) = q.comparison.inv :=
  (moduleToHomotopy R D).map_preimage _

lemma dgGluingConeRepresentativeHomInv_homotopy :
    Nonempty (ModuleHomotopy R D
      (dgGluingConeRepresentativeHom R D x y f q ≫
        dgGluingConeRepresentativeInv R D x y f q) (𝟙 _)) := by
  apply (moduleToHomotopy_map_eq_iff R D _ _).1
  simp only [CategoryTheory.Functor.map_comp, dgGluingConeRepresentativeHom_map,
    dgGluingConeRepresentativeInv_map, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
lemma dgGluingConeRepresentativeInvHom_homotopy :
    Nonempty (ModuleHomotopy R D
      (dgGluingConeRepresentativeInv R D x y f q ≫
        dgGluingConeRepresentativeHom R D x y f q) (𝟙 _)) := by
  apply (moduleToHomotopy_map_eq_iff R D _ _).1
  simp only [CategoryTheory.Functor.map_comp, dgGluingConeRepresentativeHom_map,
    dgGluingConeRepresentativeInv_map, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
