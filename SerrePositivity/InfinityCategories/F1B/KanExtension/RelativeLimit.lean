module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialComparison
public import SerrePositivity.InfinityCategories.Core.ConeOpposite
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：相対終対象と標準相対極限錐を定義し、反転した相対余極限と同定する。
方針：通常の slice の後合成の反転を coslice の後合成へ厳密な同型で移す。
規約：右 Kan の標準条件には通常の局所錐を使う。
使われ方：元の相対右 Kan 関手の局所条件と左側の制限定理の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：U に関する相対終対象は反転により相対始対象となる頂点。
方針：反転した単体集合の射に相対始対象の条件を課す。
規約：反転は単体の順序の反転。
使われ方：通常の slice の後合成で相対極限錐を定義する。 -/
@[kerodon 02KU]
def KanRelativeTerminalVertex {D E : SSet.{u}} (U : D ⟶ E) (x : D _⦋0⦌) : Prop :=
  KanRelativeInitialVertex (SSet.opFunctor.map U) (SSet.opObjEquiv.symm x)

/-- 概要：U 極限錐は通常の slice の後合成に関する相対終対象。
方針：指定した錐の頂点に相対終対象条件を課す。
規約：図式 p と標的の射 U を明示する。
使われ方：相対右 Kan 関手の元の標準局所錐の条件。 -/
@[kerodon 02KG]
def IsRelativeLimitCone {K D E : SSet.{u}} (U : D ⟶ E) {p : K ⟶ D}
    (c : JoinCone p) : Prop := KanRelativeTerminalVertex (sliceOverPostcomp p U) c

/-- 概要：通常の slice の反転同型は標的への後合成に自然。
方針：反転した錐の raw な値を計算し、反転関手の合成則を使う。
規約：元と標的の単体集合に充填性は不要。
使われ方：相対終対象と反転した相対始対象の条件を比較する。 -/
lemma kanSliceOverOpIso_postcomp {K D E : SSet.{u}} (p : K ⟶ D) (U : D ⟶ E) :
    (sliceOverOpIso p).hom ≫ sliceUnderPostcomp (SSet.opFunctor.map p) (SSet.opFunctor.map U) =
      SSet.opFunctor.map (sliceOverPostcomp p U) ≫ (sliceOverOpIso (p ≫ U)).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (sliceOverOpObjEquiv p n.unop s).val ≫ SSet.opFunctor.map U =
    (sliceOverOpObjEquiv (p ≫ U) n.unop
      ((SSet.opFunctor.map (sliceOverPostcomp p U)).app n s)).val
  rw [sliceOverOpObjEquiv_val, sliceOverOpObjEquiv_val]
  change (joinMap (𝟙 K.op) (stdSimplex.opIso n.unop).inv ≫
    (stableJoinReverseIso (stdSimplex.obj n.unop) K).inv ≫
      SSet.opFunctor.map (SSet.opObjEquiv s).val) ≫ SSet.opFunctor.map U =
    joinMap (𝟙 K.op) (stdSimplex.opIso n.unop).inv ≫
      (stableJoinReverseIso (stdSimplex.obj n.unop) K).inv ≫
        SSet.opFunctor.map ((SSet.opObjEquiv s).val ≫ U)
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- 概要：標準 U 極限錐は反転した標準相対余極限余錐と同値。
方針：通常の slice の反転同型の両成分と自然性で相対始対象性を移す。
規約：D と E のみ quasicategory とし、U の充填性は要求しない。
使われ方：右の標準局所条件を左の既存の相対条件へ渡す。 -/
lemma kanIsRelativeLimitCone_iff_reverseCocone {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) {p : K ⟶ D} (c : JoinCone p) :
    IsRelativeLimitCone U c ↔ IsRelativeColimitCone (SSet.opFunctor.map U) c.reverseCocone := by
  apply kanRelativeInitialVertex_iff_of_comparison
    (SSet.opFunctor.map (sliceOverPostcomp p U))
    (sliceUnderPostcomp (SSet.opFunctor.map p) (SSet.opFunctor.map U))
    (sliceOverOpIso p).hom (sliceOverOpIso (p ≫ U)).hom
    (kanSliceOverOpIso_postcomp p U)
    (qCatEquivalenceOfIso (sliceOverOpIso p)).isQCatEquivalence.isFullyFaithful
    (qCatEquivalenceOfIso (sliceOverOpIso (p ≫ U))).isQCatEquivalence.isFullyFaithful
  intro y
  refine ⟨(sliceOverOpIso p).inv.app (Opposite.op ⦋0⦌) y, ?_⟩
  change ((sliceOverOpIso p).inv ≫ (sliceOverOpIso p).hom).app (Opposite.op ⦋0⦌) y = y
  rw [Iso.inv_hom_id]
  rfl

end SerrePositivity.InfinityCategories.F1B
