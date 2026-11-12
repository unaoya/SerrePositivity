module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SemifreePointComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallDiagramShape
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SemifreeNativeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentCoconeTransport
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SemifreePointComparison

/-!
# 小さい添字を持つ D(A) 図式の native 余極限

## 概要
宇宙0の添字形状を持つ D(A) の全図式について、既存の bar から native 余極限の存在を得る。

## 方針
一点 dg 加群の半自由模型との同値と、添字形状の持ち上げの同型で移す。

## 規約
これは全パラメーターの余錐の族を作るための入力で、実現複体との計算比較そのものではない。

## 使われ方
HTT 4.2.4.1、HA 1.2.4。strict Δᵒᵖ 図式の native 余錐の族の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
variable (A : Type u) [CommRing A]

/-- 小さい形状を持つ既存 D(A) の図式は native な余極限を持つ。 -/
theorem smallShape_hasColimit (K : SSet.{0})
    (p : (SSet.uliftFunctor.{u + 1, 0}).obj K ⟶ derivedInfinityCategory A) :
    HasColimit p := by
  let s := smallDiagramShapeIso.{u} K
  let e := semifreePointEquivalence A
  let q := s.hom ≫ p
  obtain ⟨c, hc⟩ := dgSemifreeCoherent_hasColimit A PUnit.{1} (q ≫ e.inv)
  have he : FunctorIso ((q ≫ e.inv) ≫ e.hom) q := by
    simpa only [Category.assoc, Category.comp_id] using e.invHomIso.precomp q
  have hq : HasColimit q := (hasColimit_iff_of_functorIso he).mp
    ⟨mapJoinCocone e.hom c, (equivalence_isColimitCone_iff e.isQCatEquivalence c).mp hc⟩
  obtain ⟨d, hd⟩ := hq
  have hr : IsColimitCone (d.restrict s.inv) :=
    (isColimitCone_iff_restrict_of_isIso d s.inv).mp hd
  have hs : s.inv ≫ q = p := by
    dsimp only [q]
    rw [← Category.assoc, s.inv_hom_id, Category.id_comp]
  exact ⟨coherentCoconeOfDiagramEq hs (d.restrict s.inv),
    (coherentCoconeOfDiagramEq_isColimit_iff hs _).mp hr⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
