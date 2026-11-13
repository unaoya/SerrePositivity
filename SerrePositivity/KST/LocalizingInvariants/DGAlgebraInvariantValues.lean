module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomology
public import SerrePositivity.KST.LocalizingInvariants.ValueHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.Morita.DGAlgebraPerfectMoritaInfinity

/-!
概要：実非可換 dg 代数の Perf と実相対 tensor に、局所化不変量の値を接続する。
方針：D 所有の元の perfect nerve と完全関手を、そのまま StableCategory に束ねる。
規約：extension の厳密合成は要求しない。使われ方：dg 模型上の具体的連結度条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R]

local instance dgValueSimplicialCategory : SimplicialCategory OmegaSpectrum.{u + 1} :=
  OmegaSpectrum.simplicialCategory

def perfect (B : Mon (Complex R)) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} where
  obj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectInfinityCategory R B
  isQuasicategory := inferInstance
  isStable := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectInfinityCategory_isStable R B

def perfectMap {B C : Mon (Complex R)} (f : B ⟶ C) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (perfect R B) (perfect R C) where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectExtensionInfinity R f
  isExact := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectExtensionInfinity_isExactFunctor R f

variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

def invariantValue (B : Mon (Complex R)) : OmegaSpectrum.{u + 1} := value Φ (perfect R B)

def invariantMap {B C : Mon (Complex R)} (f : B ⟶ C) :
    invariantValue R Φ B ⟶ invariantValue R Φ C := valueMap Φ (perfectMap R f)

lemma invariantMap_edge {B C : Mon (Complex R)} (f : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := OmegaSpectrum.{u + 1}) (invariantMap R Φ f)).edge =
      Φ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (perfectMap R f)).edge :=
  valueMap_edge Φ (perfectMap R f)

def invariantGroupMap {B C : Mon (Complex R)} (f : B ⟶ C) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (invariantValue R Φ B) j →*
      OmegaSpectrum.homotopyGroup (invariantValue R Φ C) j :=
  valueHomotopyMap Φ (perfectMap R f) j

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
