module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeFunctorBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion

/-!
概要：点ごとに普遍な錐・余錐の族の、指定部分を固定した相対境界充填。
方針：各極限・余極限の相対境界充填を相対内部 Hom の一般判定へ渡す。
規約：錐・余錐の形 J は固定する。変化する slice の形の組み立ては別の工程。
使われ方：Kerodon Proposition 7.3.6.7（Tag 030F） の制限写像の証明に必要な相対余極限の充填。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：余錐の族を一つのパラメータ頂点で評価する。
方針：内部 Hom の頂点を射へ戻し、その制限を図式とする。
規約：元の族は関手 K→Fun(J⋆Δ⁰,X)。
使われ方：固定した形の余錐の点ごとの普遍性。 -/
def kanCoconeFamilyAt {J K X : SSet.{u}}
    (f : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj X) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u}) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u})) X).symm
        (f.app (Opposite.op ⦋0⦌) k)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).symm (f.app (Opposite.op ⦋0⦌) k), rfl⟩

/-- 概要：頂点で評価した余錐を再び内部 Hom の頂点にすると元の族の値。
方針：頂点と射の同値の往復。
規約：quasicategory 性は不要。
使われ方：各点の余極限性を元の族の相対境界充填へ戻す。 -/
lemma kanCoconeFamilyAt_vertex {J K X : SSet.{u}}
    (f : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj X) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (kanCoconeFamilyAt f k).val = f.app (Opposite.op ⦋0⦌) k :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).apply_symm_apply _

/-- 概要：点ごとに余極限である余錐の族は、部分パラメータを固定した相対始対象となる。
方針：各余極限を余錐の制限の相対始点境界充填へ変え、相対内部 Hom の判定に適用する。
規約：X は quasicategory、A は K の任意の部分単体集合。
使われ方：指定部分の充填と整合する普遍余錐の境界の族を延長する。 -/
lemma initialBoundaryLifting_relativeCoconeFamily_of_pointwise_colimit
    {J K X : SSet.{u}} [Quasicategory X] (A : K.Subcomplex)
    (sq' : internalHom.PullbackObjObj A.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J X))
    (f : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (kanCoconeFamilyAt f k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting sq'.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_relativeFunctor_of_pointwise A (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J X) sq' f
  intro k
  rw [← kanCoconeFamilyAt_vertex f k]
  exact (hf k).initialBoundaryLifting

/-- 概要：錐の族を一つのパラメータ頂点で評価する。
方針：内部 Hom の頂点を射へ戻し、その制限を図式とする。
規約：元の族は関手 K→Fun(Δ⁰⋆J,X)。
使われ方：固定した形の錐の点ごとの普遍性。 -/
def kanConeFamilyAt {J K X : SSet.{u}}
    (f : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J)).obj X) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) J ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J) X).symm
        (f.app (Opposite.op ⦋0⦌) k)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).symm (f.app (Opposite.op ⦋0⦌) k), rfl⟩

/-- 概要：頂点で評価した錐を再び内部 Hom の頂点にすると元の族の値。
方針：頂点と射の同値の往復。
規約：quasicategory 性は不要。
使われ方：各点の極限性を元の族の相対境界充填へ戻す。 -/
lemma kanConeFamilyAt_vertex {J K X : SSet.{u}}
    (f : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J)).obj X) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (kanConeFamilyAt f k).val = f.app (Opposite.op ⦋0⦌) k :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).apply_symm_apply _

/-- 概要：点ごとに極限である錐の族は、部分パラメータを固定した相対終対象となる。
方針：各極限を錐の制限の相対終点境界充填へ変え、相対内部 Hom の判定に適用する。
規約：X は quasicategory、A は K の任意の部分単体集合。
使われ方：指定部分の充填と整合する普遍錐の境界の族を延長する。 -/
lemma terminalBoundaryLifting_relativeConeFamily_of_pointwise_limit
    {J K X : SSet.{u}} [Quasicategory X] (A : K.Subcomplex)
    (sq' : internalHom.PullbackObjObj A.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X))
    (f : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J)).obj X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (kanConeFamilyAt f k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting sq'.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_relativeFunctor_of_pointwise A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X) sq' f
  intro k
  rw [← kanConeFamilyAt_vertex f k]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_coneRestriction_of_isLimitCone _ (hf k)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
