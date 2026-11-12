module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MHomotopyHomology

/-!
# 借用する H_* の複体模型の界面

概要：所有レーンのホモロジー関手と非被約自由整数複体のホモロジーの同定を入力する。
方針：各対象の模型同型と、全ての単体的集合の射についての自然性を保持する。
規約：H_* 自体は定義しない。KST Definition A.3、Lemma A.4 の明示的な模型界面。
使われ方：本レーンで証明した m 次ホモトピーの比較を借用関手へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：借用関手の値と自由整数複体のホモロジーの自然な模型同型。
方針：全ての対象の同型と全ての射の可換四角形だけを入力する。
規約：KST Lemma A.4、H_* は K-L2 所有。この構造体は A.4 の結論や bar の持ち上げを仮定しない。
使われ方：所有レーンの正規化模型との同定を接続するための明示的な界面。 -/
structure SimplicialHomologyModel (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (i : ℕ) where
  iso (X : SSet.{u}) : F.obj X ≅
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X)).homology i
  naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    F.map f ≫ (iso Y).hom = (iso X).hom ≫
      homologyMap ((AlgebraicTopology.alternatingFaceMapComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f)) i

/-- 概要：線形化した二つの射の m 次ホモトピーは、借用関手の次数 i≤m で同じ写像を与える。
方針：複体側で証明したホモロジー写像の一致を自然な模型同型で移す。
規約：KST Definition A.3、Lemma A.4。模型同定以外のホモロジー命題は入力しない。
使われ方：線形に持ち上げた作用 bar のホモトピーから借用 H_i の比較を得る。 -/
theorem SimplicialHomologyModel.map_eq_of_mHomotopy
    {F : SSet.{u} ⥤ ModuleCat.{u} ℤ} {i : ℕ} (M : SimplicialHomologyModel F i)
    {X Y : SSet.{u}} {f g : X ⟶ Y} {m : ℕ}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap g) m) (hi : i ≤ m) :
    F.map f = F.map g := by
  apply (cancel_mono (M.iso Y).hom).mp
  rw [M.naturality, M.naturality, H.homologyMap_eq i hi]

end SerrePositivity.KST.ProExcision
