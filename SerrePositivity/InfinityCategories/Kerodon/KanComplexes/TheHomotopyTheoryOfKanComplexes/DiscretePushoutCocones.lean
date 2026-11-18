module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscreteSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.KanPushoutCocones
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
概要：単射を一脚とする集合の指定押し出し余錐を、離散空間の余極限として保持する。
方針：定値単体集合の余極限保存と Kan 余錐の反変 Hom 判定を使う。
規約：元の集合の押し出しの頂点と脚をそのまま使い、置換はしない。
使われ方：HTT 4.2.4.1・6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）、S8-3。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 離散 Kan 関手の台は同じ定値単体集合関手である。
HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）の離散模型の表示の法則。 -/
lemma setsToKan_comp_forget :
    setsToKan.{u} ⋙ kanObjectForget = Functor.const SimplexCategoryᵒᵖ := rfl

/-- 集合の指定余錐を、同じ図式と脚の離散空間値余錐にする。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）。余極限性や単射性は構成に不要。 -/
def discreteSpaceCocone {I : Type u} [SmallCategory I] {F : I ⥤ Type u}
    (c : Cocone F) : JoinCocone (kanDiagramCoherentNerve (F ⋙ setsToKan)) :=
  coherentCoconeOfDiagramEq (strictCoherentDiagram_eq_kanDiagram (F ⋙ setsToKan))
    (strictNativeCocone (setsToKan.mapCocone c))

/-- 離散空間値余錐の頂点は、元の余錐の頂点の離散空間。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、指定頂点の保持。 -/
lemma discreteSpaceCocone_vertex {I : Type u} [SmallCategory I] {F : I ⥤ Type u}
    (c : Cocone F) :
    (discreteSpaceCocone c).vertex = coherentNerveVertex (setsToKan.obj c.pt) := by
  rw [discreteSpaceCocone, coherentCoconeOfDiagramEq_vertex, strictNativeCocone_vertex]
  rfl

/-- 集合の余極限余錐を離散 Kan 複体へ送ると、台で同じ余極限となる。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）。定値関手の余極限保存を使う。 -/
def discreteSpaceCocone_underlying_isColimit
    {I : Type u} [SmallCategory I] {F : I ⥤ Type u}
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit (kanObjectForget.mapCocone (setsToKan.mapCocone c)) := by
  change IsColimit ((Functor.const SimplexCategoryᵒᵖ).mapCocone c)
  exact isColimitOfPreserves _ hc

/-- 単射を一脚とする集合の元の押し出し余錐は、離散空間でも余極限。
HTT 4.2.4.1・6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）。
単射性なしの一般の集合の押し出しについては主張しない。 -/
lemma discreteSpaceCocone_isColimit_of_span_mono
    {F : AsSmall.{u} WalkingSpan ⥤ Type u}
    (c : Cocone F) (hc : IsColimit c)
    [Mono (F.map (AsSmall.up.map WalkingSpan.Hom.fst))] :
    IsColimitCone (discreteSpaceCocone c) := by
  have : Mono (((F ⋙ setsToKan) ⋙ kanObjectForget).map
      (AsSmall.up.map WalkingSpan.Hom.fst)) := by
    have : ∀ n, Mono ((((F ⋙ setsToKan) ⋙ kanObjectForget).map
        (AsSmall.up.map WalkingSpan.Hom.fst)).app n) :=
      fun _ ↦ inferInstanceAs (Mono (F.map (AsSmall.up.map WalkingSpan.Hom.fst)))
    exact NatTrans.mono_of_mono_app _
  exact (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
    (kanPushoutCocone_isColimitCone (setsToKan.mapCocone c)
      (discreteSpaceCocone_underlying_isColimit c hc))

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
