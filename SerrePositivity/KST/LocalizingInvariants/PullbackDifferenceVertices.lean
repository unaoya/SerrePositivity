module

public import SerrePositivity.KST.LocalizingInvariants.LaxStableCategory
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackEquivalenceIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackVertexData
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsomorphismCofiberZero

/-!
概要：通常 pullback の lax pullback への包含と、指定矢印の cofiber の消滅条件。
方針：F2 の全部分複体との厳密同型を使い、cofiber による同値判定へ接続する。
規約：ここでは cofiber の関手性・商の存在を主張しない。使われ方：Tamme Cor. 12 の核。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

/-- 元の通常 pullback の包含は全写像空間で充満忠実。 -/
lemma pullbackComparison_fullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax p.hom q.hom) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex_ι]
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso p.hom q.hom)).isQCatEquivalence.isFullyFaithful).comp
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _)

/-- 指定矢印が同値であることは元の通常 pullback の頂点から来ることと同値。 -/
lemma exists_pullbackVertex_iff (x : (laxCategory p q).obj _⦋0⦌) :
    (∃ y, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax p.hom q.hom).app (Opposite.op ⦋0⦌) y = x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsLaxEquivalenceVertex p.hom q.hom x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_vertex p.hom q.hom y
  · intro hx
    let z : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalenceSubcomplex p.hom q.hom : SSet.{u}) _⦋0⦌ :=
      ⟨x, by
        intro v
        have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
        subst v
        simpa only [op_id, CategoryTheory.Functor.map_id_apply] using hx⟩
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso p.hom q.hom
    refine ⟨e.inv.app (Opposite.op ⦋0⦌) z, ?_⟩
    have he := ConcreteCategory.congr_hom
      (NatTrans.congr_app e.inv_hom_id (Opposite.op ⦋0⦌)) z
    exact congrArg Subtype.val he

/-- 各頂点の元の指定矢印の実 cofiber 四角形。 -/
def laxDifferenceSquare (x : (laxCategory p q).obj _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackVertexData p.hom q.hom x).arrow)

/-- 差の対象の頂点での値。全単体上の関手への組み立ては後続工程。 -/
def laxDifferenceVertex (x : (laxCategory p q).obj _⦋0⦌) : E.obj _⦋0⦌ :=
  (laxDifferenceSquare p q x).cofiber

/-- 差の頂点の消滅は、指定矢印の同値性と同値。 -/
lemma laxDifferenceVertex_zero_iff (x : (laxCategory p q).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (laxDifferenceVertex p q x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsLaxEquivalenceVertex p.hom q.hom x :=
  (laxDifferenceSquare p q x).homMk_isIso_iff_zero.symm

/-- 通常 pullback は、差の cofiber が零である頂点をちょうど尽くす。 -/
lemma exists_pullbackVertex_iff_difference_zero (x : (laxCategory p q).obj _⦋0⦌) :
    (∃ y, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax p.hom q.hom).app (Opposite.op ⦋0⦌) y = x) ↔
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (laxDifferenceVertex p q x) :=
  (exists_pullbackVertex_iff p q x).trans (laxDifferenceVertex_zero_iff p q x).symm

end SerrePositivity.KST.LocalizingInvariants
