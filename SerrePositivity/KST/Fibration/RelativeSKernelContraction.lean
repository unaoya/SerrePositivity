module
public import SerrePositivity.KST.Fibration.RelativeSKernel
public import SerrePositivity.KST.Fibration.InitialVertexLocalizedContraction

/-! # Verdier 包含側の相対 S の各段の元の一点射の可逆性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 包含を通る相対 S の全単体は、元の S の全単体に厳密に同型。 -/
def relativeSKernelTopIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    (relativeSConstruction (i.hom ≫ q.hom) n : SSet.{u}) ≅ sConstruction n A.obj :=
  eqToIso (congrArg (fun P : (sConstruction n A.obj).Subcomplex => (P : SSet.{u}))
    (relativeSKernel_eq_top h n)) ≪≫ Subcomplex.topIso _

/-- 元の零対象の始対象性から、各相対 S の同じ一点への射は局所化同型。 -/
theorem relativeSKernel_toPoint_localized_isIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (terminal.from (relativeSConstruction (i.hom ≫ q.hom) n : SSet.{u}))) := by
  have := initialVertex_toPoint_localized_isIso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex (sConstruction n A.obj)).isZero.1
  have he : (relativeSKernelTopIso h n).hom ≫ terminal.from (sConstruction n A.obj) =
      terminal.from (relativeSConstruction (i.hom ≫ q.hom) n : SSet.{u}) :=
    terminal.hom_ext _ _
  rw [← he, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration
