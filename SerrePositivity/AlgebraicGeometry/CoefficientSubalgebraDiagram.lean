module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationCoefficientModel
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
概要：指定係数環上の有限生成部分代数を、実際の環の filtered 図式にする。
方針：有限集合 s を k[s] に送り、元の環への包含を cocone とする。
規約：遷移の忠実平坦性は仮定しない。元の環の Noether 性も要求しない。
使われ方：G2 の一般の有限表示対象の同じ係数段への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u v
variable (k : Type v) (R : Type u) [CommRing k] [CommRing R] [Algebra k R]

/-- 有限個の係数で生成した実際の部分代数の図式。 -/
def coefficientSubalgebraDiagram : Finset R ⥤ CommRingCat.{u} where
  obj s := .of (Algebra.adjoin k (s : Set R))
  map {s t} f := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr (leOfHom f)))).toRingHom
  map_id s := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- 同じ包含からなる、元の環 R を頂点とする cocone。 -/
def coefficientSubalgebraCocone : Cocone (coefficientSubalgebraDiagram k R) where
  pt := CommRingCat.of R
  ι.app s := CommRingCat.ofHom (Algebra.adjoin k (s : Set R)).val.toRingHom
  ι.naturality {s t} f := by ext x; rfl

/-- 各段の k-代数構造は、実際の係数部分代数の構造。 -/
instance coefficientSubalgebraDiagram_algebra (s : Finset R) :
    Algebra k ((coefficientSubalgebraDiagram k R).obj s) :=
  inferInstanceAs (Algebra k (Algebra.adjoin k (s : Set R)))

/-- 各係数段は指定した k 上有限型。 -/
instance coefficientSubalgebraDiagram_finiteType (s : Finset R) :
    Algebra.FiniteType k ((coefficientSubalgebraDiagram k R).obj s) :=
  (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)

/-- 各係数段の Noether 性は、元の環でなく指定係数環から得る。 -/
instance coefficientSubalgebraDiagram_noetherian [IsNoetherianRing k] (s : Finset R) :
    IsNoetherianRing ((coefficientSubalgebraDiagram k R).obj s) :=
  isNoetherianRing_of_fg (Subalgebra.fg_adjoin_finset s)

/-- 元の環 R は、有限生成係数部分代数と実際の包含の filtered colimit。 -/
def coefficientSubalgebraCoconeIsColimit : IsColimit (coefficientSubalgebraCocone k R) := by
  classical
  letI : ReflectsColimitsOfShape (Finset R) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro r
    exact ⟨{r}, ⟨r, Algebra.subset_adjoin (Finset.mem_singleton_self r)⟩, rfl⟩
  · intro s x y h
    refine ⟨s, 𝟙 s, ?_⟩
    exact Subtype.ext h

end SerrePositivity.AlgebraicGeometry
