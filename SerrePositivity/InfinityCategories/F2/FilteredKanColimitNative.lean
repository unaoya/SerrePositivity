module

public import SerrePositivity.InfinityCategories.F2.FilteredKanColimitComparison
public import SerrePositivity.InfinityCategories.F2.ColimitVertexTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanCoherentColimit

/-!
概要：通常の filtered Kan colimit は SpaceInfinity の実際の余極限頂点となる。
方針：N の coend 余錐を、構成した弱同値の coherent な辺に沿って移す。
規約：図式を固定した余極限余錐を得る。通常の余錐の全脚との比較は別工程。
使われ方：一般 coherent filtered 余極限の比較と有限極限との交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- 概要：通常の filtered colimit を頂点とする実際の ∞ 余極限余錐が存在する。
方針：Kan coend からの比較の同値性を可逆辺にし、N の余錐の頂点を移す。
規約：元の strict 図式の coherent nerve を固定する。使われ方：余極限余錐の選択。 -/
lemma exists_filteredKanColimitCocone (F : I ⥤ KanObject.{u}) :
    ∃ c : JoinCocone (kanDiagramCoherentNerve F),
      IsColimitCone c ∧ c.vertex = spaceInfinityVertex (filteredKanColimitObject F) := by
  let f := filteredKanColimitComparison F
  have hf := filteredKanColimitComparison_isWeakHomotopyEquivalence F
  have hi := coherentKanEdge_isInvertible_of_isQCatEquivalence
    hf.isSimplicialHomotopyEquivalence.isQCatEquivalence
  let e : SpaceInfinity.{u}.Edge (bousfieldKanCoherentCocone F).vertex
      (spaceInfinityVertex (filteredKanColimitObject F)) :=
    (coherentNerveEdge f).ofEq (by
      rw [bousfieldKanCoherentCocone_vertex, spaceInfinityVertex_eq_coherent])
      (spaceInfinityVertex_eq_coherent _).symm
  have he : IsInvertibleEdge e :=
    (isInvertibleEdge_congr (e := coherentNerveEdge f) (f := e) rfl).mp hi
  exact exists_colimitCone_vertex_of_invertible (bousfieldKanCoherentCocone F)
    (bousfieldKanCoherentCocone_isColimit F) e he

/-- 概要：通常の filtered Kan colimit を頂点に持つ SpaceInfinity の余錐。
方針：存在を証明した余極限余錐を選ぶ。
規約：頂点を変えず、図式の高次の整合性も保持する。使われ方：具体的な余極限模型。 -/
def filteredKanColimitCocone (F : I ⥤ KanObject.{u}) :
    JoinCocone (kanDiagramCoherentNerve F) :=
  Classical.choose (exists_filteredKanColimitCocone F)

/-- 概要：選ばれた filtered Kan colimit の余錐は実際の ∞ 余極限。
方針：存在証明の余極限性を取り出す。
規約：native な IsColimitCone を使う。使われ方：余極限の普遍性。 -/
lemma filteredKanColimitCocone_isColimit (F : I ⥤ KanObject.{u}) :
    IsColimitCone (filteredKanColimitCocone F) :=
  (Classical.choose_spec (exists_filteredKanColimitCocone F)).1

/-- 概要：余極限余錐の頂点は通常の単体集合の filtered colimit。
方針：存在証明で指定した頂点の等式を取り出す。
規約：選んだ coend の Kan 置換を頂点に残さない。使われ方：有限段での計算。 -/
lemma filteredKanColimitCocone_vertex (F : I ⥤ KanObject.{u}) :
    (filteredKanColimitCocone F).vertex = spaceInfinityVertex (filteredKanColimitObject F) :=
  (Classical.choose_spec (exists_filteredKanColimitCocone F)).2

end SerrePositivity.InfinityCategories.F2
