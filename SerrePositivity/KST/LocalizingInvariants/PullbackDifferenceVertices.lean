module

public import SerrePositivity.KST.LocalizingInvariants.LaxStableCategory
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackEquivalenceIso
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackVertexData
public import SerrePositivity.InfinityCategories.F1B.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Stable.IsomorphismCofiberZero

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

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

/-- 元の通常 pullback の包含は全写像空間で充満忠実。 -/
lemma pullbackComparison_fullyFaithful :
    IsFullyFaithful (F2.catPullbackToLax p.hom q.hom) := by
  rw [← F2.catPullbackToEquivalenceSubcomplex_ι]
  exact ((qCatEquivalenceOfIso
    (F2.catPullbackEquivalenceSubcomplexIso p.hom q.hom)).isQCatEquivalence.isFullyFaithful).comp
      (isFullyFaithful_fullSubcomplexOnVertices_ι _ _)

/-- 指定矢印が同値であることは元の通常 pullback の頂点から来ることと同値。 -/
lemma exists_pullbackVertex_iff (x : (laxCategory p q).obj _⦋0⦌) :
    (∃ y, (F2.catPullbackToLax p.hom q.hom).app (Opposite.op ⦋0⦌) y = x) ↔
      F2.IsLaxEquivalenceVertex p.hom q.hom x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact F2.catPullbackToLax_vertex p.hom q.hom y
  · intro hx
    let z : (F2.laxPullbackEquivalenceSubcomplex p.hom q.hom : SSet.{u}) _⦋0⦌ :=
      ⟨x, by
        intro v
        have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
        subst v
        simpa only [op_id, CategoryTheory.Functor.map_id_apply] using hx⟩
    let e := F2.catPullbackEquivalenceSubcomplexIso p.hom q.hom
    refine ⟨e.inv.app (Opposite.op ⦋0⦌) z, ?_⟩
    have he := ConcreteCategory.congr_hom
      (NatTrans.congr_app e.inv_hom_id (Opposite.op ⦋0⦌)) z
    exact congrArg Subtype.val he

/-- 各頂点の元の指定矢印の実 cofiber 四角形。 -/
def laxDifferenceSquare (x : (laxCategory p q).obj _⦋0⦌) :=
  chosenCofiberSquare (edgeOfSimplex (F2.laxPullbackVertexData p.hom q.hom x).arrow)

/-- 差の対象の頂点での値。全単体上の関手への組み立ては後続工程。 -/
def laxDifferenceVertex (x : (laxCategory p q).obj _⦋0⦌) : E.obj _⦋0⦌ :=
  (laxDifferenceSquare p q x).cofiber

/-- 差の頂点の消滅は、指定矢印の同値性と同値。 -/
lemma laxDifferenceVertex_zero_iff (x : (laxCategory p q).obj _⦋0⦌) :
    IsZeroVertex (laxDifferenceVertex p q x) ↔
      F2.IsLaxEquivalenceVertex p.hom q.hom x :=
  (laxDifferenceSquare p q x).homMk_isIso_iff_zero.symm

/-- 通常 pullback は、差の cofiber が零である頂点をちょうど尽くす。 -/
lemma exists_pullbackVertex_iff_difference_zero (x : (laxCategory p q).obj _⦋0⦌) :
    (∃ y, (F2.catPullbackToLax p.hom q.hom).app (Opposite.op ⦋0⦌) y = x) ↔
      IsZeroVertex (laxDifferenceVertex p q x) :=
  (exists_pullbackVertex_iff p q x).trans (laxDifferenceVertex_zero_iff p q x).symm

end SerrePositivity.KST.LocalizingInvariants
