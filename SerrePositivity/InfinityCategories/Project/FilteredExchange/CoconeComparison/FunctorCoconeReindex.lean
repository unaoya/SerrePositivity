module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.FunctorCoconeEvaluation

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

/-!
概要：元の coherent な余錐のパラメータを制限しても点ごとの余極限性は保たれる。
方針：前合成後の評価を元の像の点での評価へ厳密に同定する。
規約：元の余錐の全単体を保持。使われ方：filtered 交換の形状同型不変性と有限接着。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 全余錐の射が厳密に一致すれば元の余極限性も一致する。 -/
lemma isColimitCone_iff_of_coconeMap_eq {J X : SSet.{u}} {p q : J ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (h : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := by
  have hp : p = q := c.property.symm.trans
    ((congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ k) h).trans d.property)
  subst q
  have hc : c = d := Subtype.ext h
  rw [hc]

/-- パラメータの前合成後の評価は、その元の像の点での評価。 -/
lemma functorCoconePrecomp_evaluate {A B X : SSet.{u}} (f : A ⟶ B) (a : A _⦋0⦌) :
    (pre f).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (f.app (Opposite.op ⦋0⦌) a) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  change F.app (Opposite.op ⦋n⦌) (𝟙 _) (f.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a n)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
  rfl

/-- 元の余錐全体を同じパラメータの前合成で制限する。 -/
def reindexFunctorCocone {J K L X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (f : L ⟶ K) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ (pre f).app X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone ((pre f).app X) c

/-- 元の点ごとの余極限余錐は、任意のパラメータの前合成後も点ごとの余極限。 -/
lemma IsPointwiseColimitCone.reindex {J K L X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c)
    (f : L ⟶ K) : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone (reindexFunctorCocone c f) := by
  intro l
  apply (isColimitCone_iff_of_coconeMap_eq _
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c (f.app (Opposite.op ⦋0⦌) l)) ?_).mpr
    (hc (f.app (Opposite.op ⦋0⦌) l))
  change (c.val ≫ (pre f).app X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l =
    c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (f.app (Opposite.op ⦋0⦌) l)
  rw [Category.assoc, functorCoconePrecomp_evaluate]

/-- 制限した余錐の頂点も元の頂点の同じ前合成である。 -/
lemma reindexFunctorCocone_vertex {J K L X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (f : L ⟶ K) :
    (reindexFunctorCocone c f).vertex = ((pre f).app X).app (Opposite.op ⦋0⦌) c.vertex := rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
