module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyHomDifferential
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Unconditional
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeCoordinates
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
概要：指定された native 余錐から全正規化 bar の実 dg 増大射を回収する。
方針：終点固定写像空間の零単体を、B の閉次数零 Hom へ送る。
規約：同じ元の coherent 余錐の全混合 HA 成分を用いる。
使われ方：分解済み図式の余錐の擬同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgBarCoconePoint (c : JoinCocone G) : (coconeMappingSpace G c.vertex) _⦋0⦌ :=
  ⟨c, by rw [PinchedHom.constant_zero]; rfl⟩

def dgCoherentBarCoconeModuleMap (c : JoinCocone G) :
    ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarCoconeModule R D G c) :=
  moduleMorphismOfCycle R D
    (dgCoherentBarCoconeFamilyHom R D G (dgCoherentBarMaurerCartan_unconditional R D G)
      c.vertex (dgBarCoconePoint R D G c))
    (dgCoherentBarCoconeFamilyHom_closed_zero R D G
      (dgCoherentBarMaurerCartan_unconditional R D G) c.vertex (dgBarCoconePoint R D G c))

lemma dgCoherentBarCoconeModuleMap_cycle (c : JoinCocone G) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgCoherentBarCoconeModuleMap R D G c))).val =
      dgCoherentBarCoconeFamilyHom R D G (dgCoherentBarMaurerCartan_unconditional R D G)
        c.vertex (dgBarCoconePoint R D G c) :=
  moduleMorphismOfCycle_cycle R D _ _

end SerrePositivity.InfinityCategories
