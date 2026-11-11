module

public import SerrePositivity.KST.LocalizingInvariants.DGPerfectExtensionIdentityIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantComposition

/-!
概要：元の非可換 dg 代数の Perf と元の不変量の値を、h Sp 上の実関手へ束ねる。
方針：元の恒等 graph 延長の同型から恒等則を得て、検証した実合成式を使う。
規約：対象・射は元の BF 値と同じ。使われ方：dg 代数の実値の塔と pro 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

lemma dgAlgebraMap_id (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (𝟙 B) = DGFunctor.id (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) := by
  apply EnrichedFunctor.ext (Complex R) (fun x => by cases x; rfl)
  intro x y
  change (𝟙 B.X) ≫ eqToHom _ = 𝟙 B.X
  rw [eqToHom_refl, Category.id_comp]

/-- 元の代数恒等射に沿う実 Perf 延長と恒等 ∞ 関手の同型。 -/
def perfectMapIdentityIso (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (perfectMap R (𝟙 B)).hom (𝟙 _) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (𝟙 B))) (𝟙 _)
  rw [dgAlgebraMap_id]
  exact dgPerfectExtensionIdentityIso R _

variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

lemma invariantMap_id_hom (B : Mon (Complex R)) :
    SpectrumHo.hom (invariantMap R Φ (𝟙 B)) = 𝟙 _ := by
  let idP : perfect R B ⟶ perfect R B := 𝟙 _
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (perfectMap R (𝟙 B)).hom idP.hom := perfectMapIdentityIso R B
  have h := valueMap_hom_eq_of_functorIso Φ (A := perfect R B) (B := perfect R B)
    (F := perfectMap R (𝟙 B)) (G := idP) e
  exact h.trans ((stableValueFunctor Φ).map_id (perfect R B))

/-- 実 Perf と元の BF 値の射を持つ、dg 代数上の不変量値の実関手。 -/
def invariantFunctor : Mon (Complex R) ⥤ hoFunctor.obj Sp.{u + 1} where
  obj B := SpectrumHo.obj (invariantValue R Φ B)
  map f := SpectrumHo.hom (invariantMap R Φ f)
  map_id := invariantMap_id_hom R Φ
  map_comp := invariantMap_comp_hom R Φ

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
