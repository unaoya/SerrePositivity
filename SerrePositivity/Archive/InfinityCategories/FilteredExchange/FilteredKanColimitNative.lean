module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FilteredKanColimitComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FilteredKanColimitCanonical
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitVertexTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.BousfieldKanCoherentColimit

/-!
概要：通常の filtered Kan colimit は SpaceInfinity の実際の余極限頂点となる。
方針：反転 augmentation の Hom 比較から元の通常の余錐の普遍性を得る。
規約：元の通常の余錐の全ての脚と高次の整合性を保持する。
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
方針：元の通常の余錐自体の native な普遍性を使う。
規約：元の strict 図式の coherent nerve を固定する。使われ方：余極限余錐の選択。 -/
lemma exists_filteredKanColimitCocone (F : I ⥤ KanObject.{u}) :
    ∃ c : JoinCocone (kanDiagramCoherentNerve F),
      IsColimitCone c ∧ c.vertex = spaceInfinityVertex (filteredKanColimitObject F) :=
  ⟨filteredKanColimitCanonicalCocone F, filteredKanColimitCanonicalCocone_isColimit F,
    filteredKanColimitCanonicalCocone_vertex F⟩

/-- 概要：通常の filtered Kan colimit を頂点に持つ SpaceInfinity の余錐。
方針：通常の colimit の指定余錐を coherent nerve 上に表示する。
規約：頂点を変えず、図式の高次の整合性も保持する。使われ方：具体的な余極限模型。 -/
def filteredKanColimitCocone (F : I ⥤ KanObject.{u}) :
    JoinCocone (kanDiagramCoherentNerve F) :=
  filteredKanColimitCanonicalCocone F

/-- 概要：選ばれた filtered Kan colimit の余錐は実際の ∞ 余極限。
方針：指定余錐の表現可能判定による証明を使う。
規約：native な IsColimitCone を使う。使われ方：余極限の普遍性。 -/
lemma filteredKanColimitCocone_isColimit (F : I ⥤ KanObject.{u}) :
    IsColimitCone (filteredKanColimitCocone F) :=
  filteredKanColimitCanonicalCocone_isColimit F

/-- 概要：余極限余錐の頂点は通常の単体集合の filtered colimit。
方針：通常の指定余錐の頂点の式を使う。
規約：選んだ coend の Kan 置換を頂点に残さない。使われ方：有限段での計算。 -/
lemma filteredKanColimitCocone_vertex (F : I ⥤ KanObject.{u}) :
    (filteredKanColimitCocone F).vertex = spaceInfinityVertex (filteredKanColimitObject F) :=
  filteredKanColimitCanonicalCocone_vertex F

end SerrePositivity.InfinityCategories.F2
