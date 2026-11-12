module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeFamilyPostcomp

/-!
概要：像の図式を指定等式で固定する錐族の後合成。
方針：後合成の標的の錐族を図式の等式で輸送する。
規約：等式は元の射の厳密な等式として保持する。
使われ方：引き戻しの可換条件による錐族の底の一致。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：像の図式を指定等式で固定した錐族の後合成。
方針：元の後合成の標的を等式で輸送する。
規約：射影先の図式を変更せず同じ錐族で比較する。
使われ方：引き戻しの第二成分から共通の底への射。 -/
def coneFamilyPostcompOfEq {J X Y : SSet.{u}} (r : J ⟶ X) (f : X ⟶ Y)
    {s : J ⟶ Y} (h : r ≫ f = s) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily r ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily s :=
  h ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp r f

/-- 概要：図式を固定した後合成の包含は元の内部 Hom の後合成。
方針：指定等式を消去して元の後合成の式へ戻す。
規約：等式の証明の選択に依存しない。
使われ方：共通の底上での射の照合。 -/
lemma coneFamilyPostcompOfEq_ι {J X Y : SSet.{u}} (r : J ⟶ X) (f : X ⟶ Y)
    {s : J ⟶ Y} (h : r ≫ f = s) :
    coneFamilyPostcompOfEq r f h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r) ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J)).map f := by
  subst s
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp_ι r f

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
