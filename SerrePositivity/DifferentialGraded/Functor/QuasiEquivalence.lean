module
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.EssentialImage

/-! # 準同値

各 Hom の準同型と H⁰ の本質的全射を独立に要求する。
Morita 同値・通常の圏同値と同一視しない。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w} {T : Type t}
  [DGCategory A D] [DGCategory A E] [DGCategory A T]

/-- dg 関手が各 Hom 複体で準同型を誘導するという条件。 -/
def HomQuasiIso (F : DGFunctor A D E) : Prop := ∀ x y, QuasiIso (F.map x y)

/-- 準同値は Hom 準同型と H⁰ の本質的全射の二条件。 -/
def QuasiEquivalence (F : DGFunctor A D E) : Prop :=
  HomQuasiIso F ∧ F.onHomotopy.EssSurj

/-- dg 恒等関手は各 Hom で準同型。 -/
lemma homQuasiIso_id : HomQuasiIso (DGFunctor.id (A := A) D) := by
  intro x y
  change QuasiIso (𝟙 _)
  constructor
  intro i
  exact quasiIsoAt_of_isIso (𝟙 (x ⟶[Complex A] y)) i

/-- Hom 準同型条件は合成に安定。 -/
lemma homQuasiIso_comp (F : DGFunctor A D E) (G : DGFunctor A E T)
    (hF : HomQuasiIso F) (hG : HomQuasiIso G) : HomQuasiIso (DGFunctor.comp F G) := by
  intro x y
  have := hF x y
  have := hG (F.obj x) (F.obj y)
  change QuasiIso (F.map x y ≫ G.map (F.obj x) (F.obj y))
  infer_instance

/-- dg 恒等関手は準同値。 -/
lemma quasiEquivalence_id : QuasiEquivalence (DGFunctor.id (A := A) D) := by
  refine ⟨homQuasiIso_id, ?_⟩
  rw [DGFunctor.onHomotopy_id]
  infer_instance

/-- 準同値は合成に安定。二条件をそれぞれ証明する。 -/
lemma quasiEquivalence_comp (F : DGFunctor A D E) (G : DGFunctor A E T)
    (hF : QuasiEquivalence F) (hG : QuasiEquivalence G) :
    QuasiEquivalence (DGFunctor.comp F G) := by
  refine ⟨homQuasiIso_comp F G hF.1 hG.1, ?_⟩
  have := hF.2
  have := hG.2
  rw [DGFunctor.onHomotopy_comp]
  infer_instance
end SerrePositivity.DifferentialGraded
