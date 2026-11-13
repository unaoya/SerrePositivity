module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.FilteredKanColimits
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ReflectedFilteredAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.ReflectedBousfieldKanColimit

/-!
概要：N の Kan 置換した反転 coend と通常の filtered Kan colimit の比較。
方針：標準 augmentation を anodyne 単位に沿って延長し、二対三則で同値性を示す。
規約：延長の存在は Kan 標的への持ち上げから構成し、仮定にしない。
使われ方：通常の filtered colimit を SpaceInfinity の余極限頂点にする。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- 概要：通常の filtered colimit を Kan 対象として束ねる。
方針：有限ホーンの因子分解による Kan 性の保存を使う。
規約：頂点の単体集合は選ばれた通常の colimit。使われ方：具体的な余極限頂点。 -/
def filteredKanColimitObject (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := by
  have (i : I) : KanComplex ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj i) := (F.obj i).isKanComplex
  exact ⟨colimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget), inferInstance⟩

/-- 概要：反転 coend の単位と filtered colimit への augmentation の持ち上げ問題。
方針：両辺を一点へ送り、anodyne 単位の持ち上げ性を用意する。
規約：元の augmentation を上辺に保持。使われ方：実際の比較射の構成。 -/
lemma filteredKanColimitComparisonSquare (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    CommSq (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reflectedBousfieldKanAugmentation (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)))
      (terminal.from (filteredKanColimitObject F).obj)
      (terminal.from (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F).obj) :=
  ⟨terminal.hom_ext _ _⟩

instance filteredKanColimitComparison_hasLiftingProperty (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    HasLiftingProperty
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)))
      (terminal.from (filteredKanColimitObject F).obj) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit_anodyne _ _
    ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)

/-- 概要：Kan 置換した反転 coend から通常の filtered Kan colimit への比較射。
方針：anodyne 単位と Kan 標的の持ち上げ問題を解く。
規約：N の実際の余極限模型を始域に使う。使われ方：余極限頂点の同値。 -/
def filteredKanColimitComparison (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F ⟶ filteredKanColimitObject F :=
  (filteredKanColimitComparisonSquare F).lift

/-- 概要：比較射は元の反転 coend 上で指定した augmentation に一致する。
方針：持ち上げの左三角形の式。
規約：ホモトピーだけでなく射の等式。使われ方：二対三則。 -/
lemma filteredKanColimitComparison_factor (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) ≫
      filteredKanColimitComparison F = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reflectedBousfieldKanAugmentation (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  (filteredKanColimitComparisonSquare F).fac_left

/-- 概要：Kan coend と通常の filtered colimit の比較は弱ホモトピー同値。
方針：anodyne 単位と反転 augmentation の弱同値性で左因子を消去する。
規約：比較射は上で構成した持ち上げ。使われ方：coherent な可逆辺。 -/
lemma filteredKanColimitComparison_isWeakHomotopyEquivalence (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (filteredKanColimitComparison F) := by
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))) := by
    intro Z _
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit_anodyne (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))) Z
    exact h.mapPiZero_bijective
  apply hu.cancel_left
  rw [filteredKanColimitComparison_factor]
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reflectedBousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
