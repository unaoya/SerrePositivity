module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitExistenceTransfer

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinPushout
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentCoconeTransport

/-!
概要：形状の押し出し上に、共通部分の全単体で一致する二つの余錐を実際に貼り合わせる。
方針：余錐の join の押し出しを使い、元の図式の固定条件と両側への制限を証明する。
規約：充填性・余極限性は不要。貼り合わせは元の両余錐とその頂点を厳密に保つ。
使われ方：境界上の整合性を与えた部分余極限余錐から、一般の図式の余錐を組み立てる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D X : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
  (hp : IsPushout f g i j) (p : D ⟶ X)
  (cB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (cC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ cB.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 Δ[0]) ≫ cC.val)

/-- 二つの部分余錐を、元の図式を保って形状の押し出しへ貼り合わせた余錐。 -/
def coherentShapePushoutCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_isPushout hp Δ[0]).desc cB.val cC.val h, by
    apply hp.hom_ext
    · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_isPushout hp Δ[0]).inl_desc]
      exact cB.property
    · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_isPushout hp Δ[0]).inr_desc]
      exact cC.property⟩

/-- 貼り合わせた余錐を左の部分へ制限すると、元の左余錐と厳密に一致する。 -/
lemma coherentShapePushoutCocone_left :
    (coherentShapePushoutCocone hp p cB cC h).restrict i = cB := by
  apply Subtype.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_isPushout hp Δ[0]).inl_desc _ _ _

/-- 貼り合わせた余錐を右の部分へ制限すると、元の右余錐と厳密に一致する。 -/
lemma coherentShapePushoutCocone_right :
    (coherentShapePushoutCocone hp p cB cC h).restrict j = cC := by
  apply Subtype.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_isPushout hp Δ[0]).inr_desc _ _ _

/-- 貼り合わせは左の部分余錐の頂点を保つ。 -/
lemma coherentShapePushoutCocone_vertex :
    (coherentShapePushoutCocone hp p cB cC h).vertex = cB.vertex := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict (coherentShapePushoutCocone hp p cB cC h) i,
    coherentShapePushoutCocone_left]

/-- 両側の部分余錐を固定した貼り合わせは一意である。 -/
lemma coherentShapePushoutCocone_unique (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hB : c.restrict i = cB) (hC : c.restrict j = cC) :
    c = coherentShapePushoutCocone hp p cB cC h := by
  apply Subtype.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_isPushout hp Δ[0]).hom_ext
  · exact (congrArg Subtype.val hB).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_isPushout hp Δ[0]).inl_desc _ _ _).symm
  · exact (congrArg Subtype.val hC).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_isPushout hp Δ[0]).inr_desc _ _ _).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
