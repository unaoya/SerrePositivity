module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FilteredLifting

/-!
概要：Kan fibrations の filtered 図式の余極限射は Kan fibration。
方針：有限ホーンと有限単体に対する右持ち上げ性の保存を使う。
規約：追加のモデル圏構造を仮定しない。
使われ方：filtered 余極限と空間の引き戻しの交換を具体的に比較する準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra SSet
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：filtered 図式の各射が Kan fibration なら、その余極限射も Kan fibration。
方針：全ての生成ホーンの有限表示性から余極限の右持ち上げ性を得る。
規約：図式の始域・終域の Kan 性は不要。使われ方：filtered な homotopy pullback 模型。 -/
lemma fibration_of_filtered_isColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) [∀ j, Fibration (η.app j)]
    {cF : Cocone F} (hF : IsColimit cF) {cG : Cocone G} (hG : IsColimit cG)
    (p : cF.pt ⟶ cG.pt) (hp : ∀ j, cF.ι.app j ≫ p = η.app j ≫ cG.ι.app j) :
    Fibration p := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.hasLiftingProperty_of_filtered_isColimit η hF hG p hp (horn (n + 1) k).ι

/-- 概要：選ばれた filtered 余極限の間の自然変換の像は Kan fibration。
方針：余極限の射の脚上の式を一般の判定に渡す。
規約：通常の小圏による図式。使われ方：具体的な Kan 模型の射の保存。 -/
instance filteredColimitMap_fibration
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) [∀ j, Fibration (η.app j)] :
    Fibration (colim.map η) :=
  fibration_of_filtered_isColimit η (colimit.isColimit F) (colimit.isColimit G)
    (colim.map η) (fun j ↦ colimit.ι_map η j)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
