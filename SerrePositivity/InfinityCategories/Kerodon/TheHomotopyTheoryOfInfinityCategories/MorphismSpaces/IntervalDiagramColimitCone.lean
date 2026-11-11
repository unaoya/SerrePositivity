module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramOverRestriction

/-!
概要：底を覆う余極限の各項上の区間 Hom は、元の区間 Hom を厳密な極限として回収する。
方針：元の制限を反変関手へ束ね、全パラメーターの一意な貼り合わせを使う。
規約：全体の二図式と同じ区間 Hom の実際の制限錐を使う。
使われ方：Cat∞ 値分類先の Hom のセルによる降下。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {B X : SSet.{u}} (F G : B ⟶ X)

/-- 同じ二図式の間の区間 Hom と底上の全ての制限を反変関手へ束ねる。 -/
def intervalDiagramOverFunctor : (Over B)ᵒᵖ ⥤ SSet.{u} where
  obj a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a.unop.hom ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a.unop.hom ≫ G))
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G f.unop
  map_id a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_id F G a.unop
  map_comp f g := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_comp F G g.unop f.unop).symm

/-- 底上の被覆図式へ同じ区間 Hom を制限した錐。 -/
def intervalDiagramRestrictionCone {J : Type v} [Category.{w} J] (D : J ⥤ Over B) :
    Cone (D.op ⋙ intervalDiagramOverFunctor F G) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
  π :=
    { app j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction (D.obj j.unop).hom F G
      naturality {j k} f := by
        change 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction (D.obj k.unop).hom F G =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction (D.obj j.unop).hom F G ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (D.map f.unop)
        rw [Category.id_comp]
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_restriction F G (D.map f.unop)).symm }

/-- 錐の各脚は、同じ展開した区間族として厳密に整合する。 -/
lemma intervalDiagramCone_compatible {J : Type v} [Category.{w} J] (D : J ⥤ Over B)
    (s : Cone (D.op ⋙ intervalDiagramOverFunctor F G)) {j k : J} (f : j ⟶ k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (s.π.app (Opposite.op j)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (s.π.app (Opposite.op k)) ≫ (pre (D.map f).left).app X := by
  have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (s.w f.op).symm
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre F G (D.map f)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_uncurry] at h
  exact h

/-- 底を覆う余極限上の同じ区間 Hom は、各項への元の制限錐の極限。 -/
def intervalDiagramRestrictionCone_isLimit {J : Type v} [Category.{w} J]
    (D : J ⥤ Over B) (hc : IsColimit ((Over.forgetCocone B).whisker D)) :
    IsLimit (intervalDiagramRestrictionCone F G D) where
  lift s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramFamilyColimitLift ((Over.forgetCocone B).whisker D) hc F G
    (fun j ↦ s.π.app (Opposite.op j)) (intervalDiagramCone_compatible F G D s)
  fac s j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramFamilyColimitLift_fac _ hc F G _ _ j.unop
  uniq s m hm := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramFamilyColimitLift_unique ((Over.forgetCocone B).whisker D) hc F G
      (fun j ↦ s.π.app (Opposite.op j)) (intervalDiagramCone_compatible F G D s)
    intro j
    exact hm (Opposite.op j)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
