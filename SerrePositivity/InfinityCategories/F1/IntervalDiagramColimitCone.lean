module

public import SerrePositivity.InfinityCategories.F1.IntervalDiagramOverRestriction

/-!
概要：底を覆う余極限の各項上の区間 Hom は、元の区間 Hom を厳密な極限として回収する。
方針：元の制限を反変関手へ束ね、全パラメーターの一意な貼り合わせを使う。
規約：全体の二図式と同じ区間 Hom の実際の制限錐を使う。
使われ方：Cat∞ 値分類先の Hom のセルによる降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable {B X : SSet.{u}} (F G : B ⟶ X)

/-- 同じ二図式の間の区間 Hom と底上の全ての制限を反変関手へ束ねる。 -/
def intervalDiagramOverFunctor : (Over B)ᵒᵖ ⥤ SSet.{u} where
  obj a := intervalMappingSpace
    (functorVertex (a.unop.hom ≫ F)) (functorVertex (a.unop.hom ≫ G))
  map f := intervalDiagramOverPre F G f.unop
  map_id a := intervalDiagramOverPre_id F G a.unop
  map_comp f g := (intervalDiagramOverPre_comp F G g.unop f.unop).symm

/-- 底上の被覆図式へ同じ区間 Hom を制限した錐。 -/
def intervalDiagramRestrictionCone {J : Type v} [Category.{w} J] (D : J ⥤ Over B) :
    Cone (D.op ⋙ intervalDiagramOverFunctor F G) where
  pt := intervalMappingSpace (functorVertex F) (functorVertex G)
  π :=
    { app j := intervalDiagramRestriction (D.obj j.unop).hom F G
      naturality {j k} f := by
        change 𝟙 _ ≫ intervalDiagramRestriction (D.obj k.unop).hom F G =
          intervalDiagramRestriction (D.obj j.unop).hom F G ≫
            intervalDiagramOverPre F G (D.map f.unop)
        rw [Category.id_comp]
        exact (intervalDiagramOverPre_restriction F G (D.map f.unop)).symm }

/-- 錐の各脚は、同じ展開した区間族として厳密に整合する。 -/
lemma intervalDiagramCone_compatible {J : Type v} [Category.{w} J] (D : J ⥤ Over B)
    (s : Cone (D.op ⋙ intervalDiagramOverFunctor F G)) {j k : J} (f : j ⟶ k) :
    intervalMappingUncurry (s.π.app (Opposite.op j)) =
      intervalMappingUncurry (s.π.app (Opposite.op k)) ≫ (pre (D.map f).left).app X := by
  have h := congrArg intervalMappingUncurry (s.w f.op).symm
  change _ = intervalMappingUncurry (_ ≫ intervalDiagramOverPre F G (D.map f)) at h
  rw [intervalDiagramOverPre_uncurry] at h
  exact h

/-- 底を覆う余極限上の同じ区間 Hom は、各項への元の制限錐の極限。 -/
def intervalDiagramRestrictionCone_isLimit {J : Type v} [Category.{w} J]
    (D : J ⥤ Over B) (hc : IsColimit ((Over.forgetCocone B).whisker D)) :
    IsLimit (intervalDiagramRestrictionCone F G D) where
  lift s := intervalDiagramFamilyColimitLift ((Over.forgetCocone B).whisker D) hc F G
    (fun j ↦ s.π.app (Opposite.op j)) (intervalDiagramCone_compatible F G D s)
  fac s j := intervalDiagramFamilyColimitLift_fac _ hc F G _ _ j.unop
  uniq s m hm := by
    apply intervalDiagramFamilyColimitLift_unique ((Over.forgetCocone B).whisker D) hc F G
      (fun j ↦ s.π.app (Opposite.op j)) (intervalDiagramCone_compatible F G D s)
    intro j
    exact hm (Opposite.op j)

end SerrePositivity.InfinityCategories
