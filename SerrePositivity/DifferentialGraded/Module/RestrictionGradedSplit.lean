module
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Module.GradedSplit

/-! # dg加群の制限は全斉次作用に関する分裂を保つ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

/-- section/retractionの微分との可換性を要求せず、元の全次数自然性を制限する。 -/
def ModuleGradedSplit.restrict {M N P : ModuleCategory A E} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A E f g) :
    ModuleGradedSplit A D ((moduleRestriction A D E F).map f)
      ((moduleRestriction A D E F).map g) where
  retraction x n := s.retraction (F.obj (op x)).unop n
  section_ x n := s.section_ (F.obj (op x)).unop n
  inclusion_retraction x n := by
    rw [moduleRestriction_map_eval]
    exact s.inclusion_retraction (F.obj (op x)).unop n
  section_projection x n := by
    rw [moduleRestriction_map_eval]
    exact s.section_projection (F.obj (op x)).unop n
  section_retraction x n := s.section_retraction (F.obj (op x)).unop n
  inclusion_projection := by
    rw [← CategoryTheory.Functor.map_comp, s.inclusion_projection, moduleRestriction_map_zero]
  decomposition x n := by
    rw [moduleRestriction_map_eval, moduleRestriction_map_eval]
    exact s.decomposition (F.obj (op x)).unop n
  retraction_naturality x y p i j hij a :=
    s.retraction_naturality (F.obj (op x)).unop (F.obj (op y)).unop p i j hij
      ((F.map (op x) (op y)).f p a)
  section_naturality x y p i j hij a :=
    s.section_naturality (F.obj (op x)).unop (F.obj (op y)).unop p i j hij
      ((F.map (op x) (op y)).f p a)

end SerrePositivity.DifferentialGraded
