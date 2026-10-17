module
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.HomotopyAdjunction

/-! # U13 enhancementのH⁰への実際のtensor–Hom随伴制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

def perfectEndomorphismTensorHomotopyInclusionIso :
    (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onHomotopy ⋙
        (endomorphismModuleTensor A D E.val).onHomotopy ≅
      (perfectEndomorphismTensorDG A D S E).onHomotopy ⋙
        (perfectDGModuleInclusion A D S).onHomotopy :=
  eqToIso ((DGFunctor.onHomotopy_comp _ _).symm.trans
    ((congrArg DGFunctor.onHomotopy
      (perfectEndomorphismTensorDG_inclusion_square A D S E).symm).trans
        (DGFunctor.onHomotopy_comp _ _)))

variable (hgen : endomorphismThickGeneratesPerfect A D S E)

def perfectEndomorphismHomHomotopyInclusionIso :
    (perfectDGModuleInclusion A D S).onHomotopy ⋙
        (endomorphismModuleHom A D E.val).onHomotopy ≅
      (perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
        (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onHomotopy :=
  eqToIso ((DGFunctor.onHomotopy_comp _ _).symm.trans
    ((congrArg DGFunctor.onHomotopy
      (perfectEndomorphismDG_inclusion_square A D S E hgen).symm).trans
        (DGFunctor.onHomotopy_comp _ _)))

/-- 実際のH⁰ tensorとHomの随伴。選択された逆関手で置換しない。 -/
def perfectEndomorphismEnhancementHomotopyAdjunction :
    (perfectEndomorphismTensorDG A D S E).onHomotopy ⊣
      (perfectEndomorphismDG A D S E hgen).onHomotopy :=
  (endomorphismHomotopyAdjunction A D E.val).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onHomotopy)
    (Functor.FullyFaithful.ofFullyFaithful (perfectDGModuleInclusion A D S).onHomotopy)
    (perfectEndomorphismTensorHomotopyInclusionIso A D S E)
    (perfectEndomorphismHomHomotopyInclusionIso A D S E hgen)

end SerrePositivity.DifferentialGraded
