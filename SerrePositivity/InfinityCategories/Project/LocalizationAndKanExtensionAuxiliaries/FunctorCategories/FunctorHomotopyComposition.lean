module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：二つの指定ホモトピーを、両辺の代表を保持した三角形で合成する。
方針：合成の類の辺代表を取り、指定した前辺・後辺の合成三角形を補う。
規約：合成の代表だけでなく、元の二辺を持つ二単体も保持する。
使われ方：B1 の comma 正方形から得た二つの経路の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：二つのホモトピーは指定した二辺を持つ実際の三角形で合成できる。
方針：h Fun の合成の辺代表を選び、三辺固定の三角形の存在を使う。
規約：標的が quasicategory、パラメータは任意。
使われ方：元の二つの経路を入力にした合成の選択。 -/
lemma exists_functorHomotopyComposite {A X : SSet.{u}} [Quasicategory X]
    {U V W : A ⟶ X} (l : SSet.Homotopy U V) (r : SSet.Homotopy V W) :
    ∃ d : SSet.Homotopy U W, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) := by
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W)
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k) = k := by
    ext
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm k.edge))) = k.edge
    rw [curry_uncurry, Equiv.apply_symm_apply]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.nonempty_functorCompositionTriangle_of_homEq l r _ ?_⟩
  rw [he, hk]

/-- 概要：指定二辺の合成ホモトピーを選ぶ。
方針：三角形つきの合成の存在から取り出す。
規約：対応する二単体は functorHomotopyCompositeTriangle で公開する。
使われ方：coherence を保持する経路の合成。 -/
noncomputable def functorHomotopyComposite {A X : SSet.{u}} [Quasicategory X]
    {U V W : A ⟶ X} (l : SSet.Homotopy U V) (r : SSet.Homotopy V W) : SSet.Homotopy U W :=
  (exists_functorHomotopyComposite l r).choose

/-- 概要：選んだ合成は元の二つのホモトピーと同じ三角形に入る。
方針：合成の存在証明の仕様から二単体を取り出す。
規約：二辺は入力の代表そのもの。
使われ方：合成後の経路と二つの元の経路の整合性。 -/
noncomputable def functorHomotopyCompositeTriangle {A X : SSet.{u}} [Quasicategory X]
    {U V W : A ⟶ X} (l : SSet.Homotopy U V) (r : SSet.Homotopy V W) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r (functorHomotopyComposite l r) :=
  (exists_functorHomotopyComposite l r).choose_spec.some

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
