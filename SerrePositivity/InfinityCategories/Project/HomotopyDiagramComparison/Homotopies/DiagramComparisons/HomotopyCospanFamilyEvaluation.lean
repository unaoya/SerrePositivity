module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.HomotopyCospanConeComparison

/-!
概要：任意のパラメータ族の共通 path end への像を、元の二枝と指定ホモトピーの全成分で計算する。
方針：重み付き切断の射影と自然変換の後合成を計算し、curry を外して全パラメータを読む。
規約：経路の置換への自然変換全体を保持。使われ方：余錐の全 Hom の族の end 内での照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {L M R L' M' R' : SSet.{u}} [KanComplex M']
  (f' : L' ⟶ M') (g' : R' ⟶ M') (f : L ⟶ M) (g : R ⟶ M)
  (a : L ⟶ L') (b : M ⟶ M') (c : R ⟶ R')
  (Hf : SSet.Homotopy (f ≫ b) (a ≫ f')) (Hg : SSet.Homotopy (g ≫ b) (c ≫ g'))
  (t : Cone ((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g))

/-- 共通 path end への実際の比較の射影は、元の錐の成分と指定経路の比較の後合成。 -/
lemma homotopyCospanConeComparison_π (k : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanConeComparison f' g' f g a b c Hf Hg t ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanPathDiagram f' g') k =
      curry (snd ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj k) t.pt ≫ t.π.app k) ≫
        (ihom ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj k)).map
          ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMap f' g' f g a b c Hf Hg).app k) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanConeComparison, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMapEnd,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π]

/-- curry を外すと、重みの全単体でも元の錐の成分と指定ホモトピーの自然変換を保持する。 -/
lemma homotopyCospanConeComparison_uncurry (k : AsSmall.{u} WalkingCospan) :
    uncurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanConeComparison f' g' f g a b c Hf Hg t ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanPathDiagram f' g') k) =
      snd ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj k) t.pt ≫
        t.π.app k ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMap f' g' f g a b c Hf Hg).app k := by
  rw [homotopyCospanConeComparison_π, uncurry_natural_right, uncurry_curry, Category.assoc]

/-- 任意の族を前合成しても、その全パラメータと重みの全単体で同じ成分公式を持つ。 -/
lemma homotopyCospanFamilyComparison_uncurry {T : SSet.{u}} (s : T ⟶ t.pt)
    (k : AsSmall.{u} WalkingCospan) :
    uncurry ((s ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanConeComparison f' g' f g a b c Hf Hg t) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanPathDiagram f' g') k) =
      snd ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj k) T ≫ s ≫
        t.π.app k ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMap f' g' f g a b c Hf Hg).app k := by
  rw [Category.assoc, uncurry_natural_left, homotopyCospanConeComparison_uncurry]
  simp only [← Category.assoc, whiskerLeft_snd]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
