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
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((inclusion.hom ≫ projection.hom).app (Opposite.op ⦋0⦌) a)
  generates_kernel (x : T.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (projection.hom.app (Opposite.op ⦋0⦌) x) → x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage inclusion

attribute [instance] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.counit_isIso

namespace SemiorthogonalDecomposition

variable {A B T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition A B T)

/-- 零化は包含の本質像全体に広がる。 -/
lemma kernel (x : T.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (d.projection.hom.app (Opposite.op ⦋0⦌) x) ↔
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

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.casesOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.counit_isIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.counit_isIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.counit_isIso

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.ctorIdx := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.generates_kernel := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.generates_kernel

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.inclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.inclusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.inclusion_fullyFaithful := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.inclusion_fullyFaithful

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.isVerdier := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.isVerdier

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.kernel := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.kernel

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.kills_inclusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.kills_inclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.leftAdjunction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.leftAdjunction := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.leftAdjunction

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.mk := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.noConfusionType := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.projection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.projection := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.projection

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.rec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.recOn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.retraction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.retraction := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.retraction

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.rightAdjunction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.rightAdjunction := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.rightAdjunction

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.rightInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.rightInclusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.rightInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.rightInclusion_fullyFaithful := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.rightInclusion_fullyFaithful

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.sectionIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.sectionIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.sectionIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.semiorthogonal := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.semiorthogonal

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.verdierSequence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.verdierSequence := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.verdierSequence

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.mk.inj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.mk.injEq := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition.mk.sizeOf_spec
