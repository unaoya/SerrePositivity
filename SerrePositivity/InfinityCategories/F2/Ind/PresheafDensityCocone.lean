module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityDiagramHomotopy
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeOfHomotopyConstant

/-!
概要：元の F を頂点とする、元の小さい Yoneda 図式の native な全余錐を構成する。
方針：構成済みの同じ自然変換を、頂点固定の円柱を保持して全余錐へ実現する。
規約：余極限性は別工程。元の図式と元の前層の頂点を変更しない。
使われ方：HTT 5.1.5.3 の小さい生成表示の余錐、およびその評価による余極限性の検査。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 同じ密度自然変換の全円柱を保持した、元の小さい図式上の実現データ。 -/
def presheafDensityCoconeRealization : HomotopyConstCoconeRealization
    (presheafElementsYonedaDiagram F) (functorVertex F) (presheafDensityDiagramHomotopy F) :=
  Classical.choice (homotopyConstCoconeRealization_nonempty _ _ _)

/-- 元の F を指定頂点とする、同じ小さい Yoneda 図式の全余錐。 -/
def presheafDensityCocone : JoinCocone (presheafElementsYonedaDiagram F) :=
  (presheafDensityCoconeRealization F).cocone

/-- 構成した小さい生成余錐の頂点は、元の前層 F そのもの。 -/
lemma presheafDensityCocone_vertex : (presheafDensityCocone F).vertex = functorVertex F :=
  (presheafDensityCoconeRealization F).vertex

end SerrePositivity.InfinityCategories.F2.Ind
