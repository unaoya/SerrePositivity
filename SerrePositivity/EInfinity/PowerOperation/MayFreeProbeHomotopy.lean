module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# May の代表元独立性のための自由 probe

May, Proposition 2.3 の代表元独立性の補助。
構成済みの自由 cofibrant probe は擬同型を保つため、
ホモトピックな複体射は自由 probe の全ホモロジーで同じ射になる。
テンソルのホモトピーを同変ホモトピーへ読み替えない。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.BarrattEccles
variable (k : Type u) [CommRing k]

/-- 元の自由 probe の全次数ホモロジー関手。 -/
def mayFreeProbeHomologyFunctor (i : ℤ) : Complex k ⥤ ModuleCat k :=
  freeProbeFunctor k ⋙ SerrePositivity.EInfinity.Operad.Algebra.forget (operad k) ⋙
    homologyFunctor (ModuleCat k) (.up ℤ) i

lemma mayFreeProbeHomologyFunctor_inverts (i : ℤ) :
    (HomologicalComplex.quasiIso (ModuleCat k) (.up ℤ)).IsInvertedBy
      (mayFreeProbeHomologyFunctor k i) := by
  intro K L f hf
  have hq : QuasiIso f := hf
  have : QuasiIso (((freeProbeFunctor k).map f).hom) :=
    freeProbeFunctor_map_quasiIso k f hq
  change IsIso (homologyMap (((freeProbeFunctor k).map f).hom) i)
  infer_instance

/-- ホモトピックな二射は、同じ自由 probe のホモロジーで一致する。 -/
lemma mayFreeProbeHomology_homotopy {K L : Complex k} {f g : K ⟶ L}
    (H : Homotopy f g) (i : ℤ) :
    homologyMap (((freeProbeFunctor k).map f).hom) i =
      homologyMap (((freeProbeFunctor k).map g).hom) i := by
  exact (ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization H).map_eq_of_isInvertedBy
    (mayFreeProbeHomologyFunctor k i) (mayFreeProbeHomologyFunctor_inverts k i)

end SerrePositivity.EInfinity.PowerOperation
