module
public import SerrePositivity.DifferentialGraded.Module.Acyclic
public import SerrePositivity.DifferentialGraded.Module.Yoneda
public import SerrePositivity.DifferentialGraded.Module.Zero

/-! # dg 加群の homotopically projective 性

全次数 Hom end が objectwise acyclic 加群を acyclic 複体へ送る性質。
各評価複体の K-projective 性で代用せず、Mathlib の複体 IsKProjective とは区別する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全次数の Hom end が acyclic 加群を消すという dg 加群の性質。 -/
def moduleHomotopicallyProjective : ObjectProperty (ModuleCategory A D) :=
  fun M => ∀ N : ModuleCategory A D, moduleAcyclic A D N →
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).Acyclic

/-- dg Yoneda により右代表加群は任意の小さい dg 圏上で homotopically projective。
Hom_D の A 上のprojectivityやflatnessは不要。 -/
lemma representable_homotopicallyProjective (x : D) :
    moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) (representable A x)) := by
  intro N hN i
  exact (hN x i).of_iso (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).symm

/-- この性質は主加群圏の真の同型で不変。 -/
lemma moduleHomotopicallyProjective_of_iso {M P : ModuleCategory A D} (e : M ≅ P)
    (hM : moduleHomotopicallyProjective A D M) : moduleHomotopicallyProjective A D P := by
  intro N hN i
  exact (hM N hN i).of_iso
    (((eHomFunctor (Complex A) (ModuleCategory A D)).mapIso e.op).app N).symm

instance moduleHomotopicallyProjectiveClosedUnderIso :
    (moduleHomotopicallyProjective A D).IsClosedUnderIsomorphisms where
  of_iso := moduleHomotopicallyProjective_of_iso A D

/-- 零加群も Hom end の意味で homotopically projective。 -/
lemma moduleHomotopicallyProjective_of_isZero {M : ModuleCategory A D} (hM : IsZero M) :
    moduleHomotopicallyProjective A D M := by
  intro N _ i
  have hz := moduleHom_isZero_src A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) ((module_isZero_iff A D M).1 hM)
  exact HomologicalComplex.ExactAt.of_isZero
    ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).map_isZero hz)

end SerrePositivity.DifferentialGraded
