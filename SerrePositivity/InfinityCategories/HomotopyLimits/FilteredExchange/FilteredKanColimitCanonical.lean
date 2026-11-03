module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.FilteredKanColimitComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.KanCoconeAugmentationCriterion
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.ReflectedFilteredAugmentation
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNativeCocones
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedColimit

/-!
概要：通常の filtered Kan colimit の指定余錐自体は SpaceInfinity の余極限余錐。
方針：反転 augmentation の弱同値性を元の余錐の表現可能な判定に渡す。
規約：余錐の全ての脚と高次の整合性は通常の指定余錐から得る。
使われ方：filtered 余極限の有限極限との交換に使う標準模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- 概要：通常の単体集合の colimit の脚を持つ Kan 対象の余錐。
方針：filtered colimit の Kan 性で頂点を束ね、元の脚をそのまま使う。
規約：脚は選ばれた colimit.ι。使われ方：元の余錐を保った native 表示。 -/
def filteredKanColimitOrdinaryCocone (F : I ⥤ KanObject.{u}) : Cocone F where
  pt := filteredKanColimitObject F
  ι := {
    app i := colimit.ι (F ⋙ kanObjectForget) i
    naturality i j f := by
      change (F ⋙ kanObjectForget).map f ≫ colimit.ι (F ⋙ kanObjectForget) j =
        colimit.ι (F ⋙ kanObjectForget) i ≫ 𝟙 _
      rw [Category.comp_id]
      exact colimit.w (F ⋙ kanObjectForget) f }

/-- 概要：構成した Kan 余錐の台は元の選ばれた通常の余極限余錐。
方針：頂点と脚の定義を使う。
規約：頂点だけでなく余錐全体の等式。使われ方：augmentation の一致。 -/
lemma filteredKanColimitOrdinaryCocone_forget (F : I ⥤ KanObject.{u}) :
    kanObjectForget.mapCocone (filteredKanColimitOrdinaryCocone F) =
      colimit.cocone (F ⋙ kanObjectForget) := by rfl

/-- 概要：通常の filtered Kan colimit の元の余錐は native な ∞ 余極限。
方針：元の反転 augmentation の弱同値性で全 Hom 比較を検査する。
規約：余錐を同じ頂点の別の余錐へ取り替えない。使われ方：標準余錐の普遍性。 -/
lemma filteredKanColimitOrdinaryCocone_isColimit (F : I ⥤ KanObject.{u}) :
    IsColimitCone (strictNativeCocone (filteredKanColimitOrdinaryCocone F)) := by
  apply strictNativeCocone_isColimit_of_reflectedAugmentation_weak
  rw [filteredKanColimitOrdinaryCocone_forget]
  exact reflectedBousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered _

/-- 概要：元の通常の余極限余錐を標準の Kan 図式の coherent nerve 上に表示する。
方針：strictNativeCocone の図式の表示だけを正規化する。
規約：join からの余錐の射は変えない。使われ方：既存の native な余錐 API。 -/
def filteredKanColimitCanonicalCocone (F : I ⥤ KanObject.{u}) :
    JoinCocone (kanDiagramCoherentNerve F) :=
  coherentCoconeOfDiagramEq (strictCoherentDiagram_eq_kanDiagram F)
    (strictNativeCocone (filteredKanColimitOrdinaryCocone F))

/-- 概要：標準図式上に戻した元の通常の余錐は実際の ∞ 余極限。
方針：図式の等式による移送は普遍性を保つ。
規約：全ての次数で元の余錐を使う。使われ方：filtered colimit の公開界面。 -/
lemma filteredKanColimitCanonicalCocone_isColimit (F : I ⥤ KanObject.{u}) :
    IsColimitCone (filteredKanColimitCanonicalCocone F) :=
  (coherentCoconeOfDiagramEq_isColimit_iff (strictCoherentDiagram_eq_kanDiagram F)
    (strictNativeCocone (filteredKanColimitOrdinaryCocone F))).mp
      (filteredKanColimitOrdinaryCocone_isColimit F)

/-- 概要：標準余錐の頂点は通常の単体集合の filtered colimit。
方針：図式の表示の移送と strict 余錐の頂点の式を使う。
規約：頂点の表示だけを既存の SpaceInfinity の表示に戻す。使われ方：公開余錐の頂点。 -/
lemma filteredKanColimitCanonicalCocone_vertex (F : I ⥤ KanObject.{u}) :
    (filteredKanColimitCanonicalCocone F).vertex =
      spaceInfinityVertex (filteredKanColimitObject F) := by
  rw [filteredKanColimitCanonicalCocone, coherentCoconeOfDiagramEq_vertex,
    strictNativeCocone_vertex]
  exact (spaceInfinityVertex_eq_coherent _).symm

end SerrePositivity.InfinityCategories.F2
