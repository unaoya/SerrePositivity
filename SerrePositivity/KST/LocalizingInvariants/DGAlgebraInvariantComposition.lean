module

public import SerrePositivity.KST.LocalizingInvariants.DGPerfectExtensionCompositionIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantValues
public import SerrePositivity.KST.LocalizingInvariants.StableValueFunctor

/-!
概要：元の非可換 dg 代数の Perf 延長と局所化不変量の値が、合成と整合する。
方針：元の実 Perf 合成同型を、一対象 dg 関手と元の Sp 値のホモトピー圏へ送る。
規約：実 Perf と元の BF 値の射を保持。使われ方：dg 代数の実値の塔の合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C D : Mon (Complex R)}

lemma dgAlgebraMap_comp (f : B ⟶ C) (g : C ⟶ D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R g) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (f ≫ g) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change (f.hom ≫ g.hom) ≫ eqToHom _ = (f ≫ g).hom
  rw [eqToHom_refl, Category.comp_id]
  rfl

/-- D の元の実 Perf 延長は、代数射の合成と実関手同型で整合する。 -/
def perfectMapCompositionIso (f : B ⟶ C) (g : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((perfectMap R f).hom ≫ (perfectMap R g).hom)
      (perfectMap R (f ≫ g)).hom := by
  have e := dgPerfectExtensionCompositionIso R _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R g)
  rw [dgAlgebraMap_comp] at e
  exact e

variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

lemma invariantMap_comp_hom (f : B ⟶ C) (g : C ⟶ D) :
    SpectrumHo.hom (invariantMap R Φ (f ≫ g)) =
      SpectrumHo.hom (invariantMap R Φ f) ≫ SpectrumHo.hom (invariantMap R Φ g) := by
  let fg : perfect R B ⟶ perfect R D := perfectMap R f ≫ perfectMap R g
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso fg.hom (perfectMap R (f ≫ g)).hom := perfectMapCompositionIso R f g
  have h := valueMap_hom_eq_of_functorIso Φ
    (A := perfect R B) (B := perfect R D)
    (F := fg) (G := perfectMap R (f ≫ g)) e
  exact h.symm.trans ((stableValueFunctor Φ).map_comp (perfectMap R f) (perfectMap R g))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
