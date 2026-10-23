module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramColimitFamily

/-!
概要：両端固定の区間 Hom の整合する族の、一意な大域的貼り合わせ。
方針：同じ貼り合わせを固定端点の空間へ戻し、展開の単射性で普遍性を証明する。
規約：各脚で元の同じ区間族を厳密に回収する。
使われ方：分類先の実際の Hom の底に関する降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {J : Type v} [Category.{w} J] {D : J ⥤ SSet.{u}} {T X : SSet.{u}}
  (c : Cocone D) (hc : IsColimit c) (F G : c.pt ⟶ X)
  (s : ∀ j, T ⟶ intervalMappingSpace
    (functorVertex (c.ι.app j ≫ F)) (functorVertex (c.ι.app j ≫ G)))
  (hs : ∀ {j k} (f : j ⟶ k), intervalMappingUncurry (s j) =
    intervalMappingUncurry (s k) ≫ (pre (D.map f)).app X)

/-- 同じ各区間族を、元の二図式の間の両端固定の空間へ貼る。 -/
def intervalDiagramFamilyColimitLift :
    T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G) :=
  intervalMappingCurryOfEndpoints (intervalDiagramFamilyColimitUncurry c hc F G s hs)
    (intervalDiagramFamilyColimitUncurry_zero c hc F G s hs)
    (intervalDiagramFamilyColimitUncurry_one c hc F G s hs)

/-- 貼った区間 Hom の族の展開は、元の同じ二変数の貼り合わせ。 -/
lemma intervalDiagramFamilyColimitLift_uncurry :
    intervalMappingUncurry (intervalDiagramFamilyColimitLift c hc F G s hs) =
      intervalDiagramFamilyColimitUncurry c hc F G s hs :=
  intervalMappingUncurry_curryOfEndpoints _ _ _

/-- 大域的な区間 Hom の族は、各脚で元の同じ区間 Hom の族を回収する。 -/
lemma intervalDiagramFamilyColimitLift_fac (j : J) :
    intervalDiagramFamilyColimitLift c hc F G s hs ≫
      intervalDiagramRestriction (c.ι.app j) F G = s j := by
  apply intervalMappingUncurry_injective
  rw [intervalDiagramRestriction_uncurry, intervalDiagramFamilyColimitLift_uncurry,
    intervalDiagramFamilyColimitUncurry_fac]

/-- 元の各脚を回収する大域的な区間 Hom の族は一意。 -/
lemma intervalDiagramFamilyColimitLift_unique
    (m : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G))
    (hm : ∀ j, m ≫ intervalDiagramRestriction (c.ι.app j) F G = s j) :
    m = intervalDiagramFamilyColimitLift c hc F G s hs := by
  apply intervalMappingUncurry_injective
  rw [intervalDiagramFamilyColimitLift_uncurry]
  apply functorSpaceColimit_hom_ext c hc
  intro j
  rw [intervalDiagramFamilyColimitUncurry_fac]
  rw [← intervalDiagramRestriction_uncurry, hm j]

end SerrePositivity.InfinityCategories
