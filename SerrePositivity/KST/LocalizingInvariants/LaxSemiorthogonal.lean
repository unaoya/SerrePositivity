module

public import SerrePositivity.KST.LocalizingInvariants.LaxCAdjunction
public import SerrePositivity.KST.LocalizingInvariants.LaxProjectionKernel
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition

/-!
概要：元の lax pullback の、D と C による二項半直交分解。
方針：構成済みの両完全包含・実随伴・可逆余単位と核の同定を束ねる。
規約：射影は F2 の元の射影。使われ方：Tamme Prop. 10 と局所化不変量の分裂。
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

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

/-- 順序 ⟨D,C⟩ で、左包含と右包含は元の全単体上の関手である。 -/
def laxSemiorthogonal : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition D C (laxCategory p q) where
  inclusion := LaxInclusion.exactFromD p q
  rightInclusion := LaxInclusion.exactFromC p q
  retraction := laxSnd p q
  projection := laxFst p q
  leftAdjunction := LaxInclusion.fromDAdjunction p q
  rightAdjunction := LaxInclusion.fromCAdjunction p q
  inclusion_fullyFaithful := LaxInclusion.fromD_fullyFaithful p q
  rightInclusion_fullyFaithful := LaxInclusion.fromC_fullyFaithful p q
  counit_isIso := LaxInclusion.fromCAdjunction_counit_isIso p q
  kills_inclusion a := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((LaxInclusion.fromD p q ≫ (laxFst p q).hom).app _ a)
    rw [LaxInclusion.fromD_fst, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C.obj).isZero
  generates_kernel x := (LaxInclusion.fst_kernel p q x).1

/-- 第一射影を商とする、元の lax pullback の切断付き Verdier 列。 -/
def laxVerdierSequence : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u} := (laxSemiorthogonal p q).verdierSequence

lemma laxVerdierSequence_inclusion : (laxVerdierSequence p q).inclusion =
    LaxInclusion.exactFromD p q := rfl

lemma laxVerdierSequence_projection : (laxVerdierSequence p q).projection = laxFst p q := rfl

end SerrePositivity.KST.LocalizingInvariants
