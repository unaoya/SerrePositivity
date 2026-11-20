module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.AdjointVerdier
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IntervalMappingContractible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence

/-!
概要：二項の半直交分解を、完全包含・実随伴・零化・核の生成で定義する。
方針：右因子への反射射影の核を左因子が尽くす、admissible な表示を使う。
規約：順序 ⟨A,B⟩ では Map(i A,j B) が可縮。商の普遍性は後で証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition
end SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 選ばれた随伴を持つ二項半直交分解。核の生成は零化の逆向きのみを要求する。 -/
structure SemiorthogonalDecomposition (A B T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) where
  inclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A T
  rightInclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B T
  retraction : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap T A
  projection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap T B
  leftAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction inclusion.hom retraction.hom
  rightAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction projection.hom rightInclusion.hom
  inclusion_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful inclusion.hom
  rightInclusion_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful rightInclusion.hom
  counit_isIso : IsIso rightAdjunction.counit
  kills_inclusion (a : A.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((inclusion.hom ≫ projection.hom).app (Opposite.op ⦋0⦌) a)
  generates_kernel (x : T.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (projection.hom.app (Opposite.op ⦋0⦌) x) → x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage inclusion

attribute [instance] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.counit_isIso

namespace SemiorthogonalDecomposition

variable {A B T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition A B T)

/-- 零化は包含の本質像全体に広がる。 -/
lemma kernel (x : T.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (d.projection.hom.app (Opposite.op ⦋0⦌) x) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage d.inclusion := by
  constructor
  · exact d.generates_kernel x
  · rintro ⟨a, ⟨e⟩⟩
    exact (d.kills_inclusion a).of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e d.projection.hom)

/-- 射影と右因子の包含の合成は、元の余単位を順射とする関手同型。 -/
def sectionIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.rightInclusion.hom ≫ d.projection.hom) (𝟙 B.obj) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.counitIso d.rightAdjunction

/-- 商の普遍性は随伴から導出し、半直交分解の入力にしない。 -/
lemma isVerdier : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence d.inclusion d.projection :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.isVerdierSequence_of_adjoint d.inclusion d.projection d.rightInclusion
    d.inclusion_fullyFaithful d.kernel d.rightAdjunction

/-- 半直交分解が誘導する、元の包含・射影を持つ抽象 Verdier 列。 -/
def verdierSequence : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u} where
  left := A
  middle := T
  right := B
  inclusion := d.inclusion
  projection := d.projection
  isVerdier := d.isVerdier

/-- 左因子から右因子への写像空間は可縮。 -/
lemma semiorthogonal (a : A.obj _⦋0⦌) (b : B.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (d.inclusion.hom.app (Opposite.op ⦋0⦌) a)
      (d.rightInclusion.hom.app (Opposite.op ⦋0⦌) b)) := by
  apply (d.rightAdjunction.pinchedHomEquivalence _ b).isContractibleKan
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftRightEquivalence _ _).isContractibleKan
    ((d.kills_inclusion a).1.pinchedHomLeft_isContractibleKan b)

end SemiorthogonalDecomposition
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
