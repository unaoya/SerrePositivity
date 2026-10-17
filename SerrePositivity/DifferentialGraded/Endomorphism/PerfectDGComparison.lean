module
public import SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveImage
public import SerrePositivity.DifferentialGraded.Endomorphism.QuasiFullyFaithful

/-! # U13のperfect dg enhancement間の実際の再構成Hom比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

/-- Hom像の射影性・perfect性の証拠を保持した、実際のdg enhancement間の関手。 -/
def perfectEndomorphismDG :
    DGFunctor A (PerfectDGModuleOver A D S) (PerfectDGModule A (EndomorphismObject E.val)) where
  obj M := ⟨(perfectEndomorphismModuleHom A D S E).obj M,
    perfectEndomorphismHom_obj_projective A D S E hgen M,
    perfectEndomorphismHom_obj_perfect A D S E hgen M⟩
  map M N := (perfectEndomorphismModuleHom A D S E).map M N
  map_id M := (perfectEndomorphismModuleHom A D S E).map_id M
  map_comp M N P := (perfectEndomorphismModuleHom A D S E).map_comp M N P

/-- enhancement間の各Hom写像の擬同型。本質的全射とは分けて保持する。 -/
lemma perfectEndomorphismDG_homQuasiIso : HomQuasiIso (perfectEndomorphismDG A D S E hgen) :=
  perfectEndomorphismModuleHom_homQuasiIso A D S E hgen

instance perfectEndomorphismDGHomotopyFull :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.Full :=
  dgHomMap_onHomotopy_full _ (perfectEndomorphismDG_homQuasiIso A D S E hgen)

instance perfectEndomorphismDGHomotopyFaithful :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.Faithful :=
  dgHomMap_onHomotopy_faithful _ (perfectEndomorphismDG_homQuasiIso A D S E hgen)

/-- 実際の加群への包含は、元のHom関手とdgレベルで可換。 -/
lemma perfectEndomorphismDG_inclusion_square :
    (perfectEndomorphismDG A D S E hgen).comp
        (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ) =
      perfectEndomorphismModuleHom A D S E := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (perfectEndomorphismDG A D S E hgen).comp
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ))
    (G := perfectEndomorphismModuleHom A D S E) (fun _ => rfl)
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.DifferentialGraded
