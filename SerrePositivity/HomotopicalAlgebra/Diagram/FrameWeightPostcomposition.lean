module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
概要：左随伴による後合成と、指定frame重み実現の交換。
方針：各frameの随伴Hom同型を束ね、同じ右随伴の左随伴の一意性を使う。
使われ方：HTT 4.2.4.4、RR02(a)で図式の評価と実現を交換する。
規約：実現の同型であり、増大射の弱同値性を前提にしない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u v
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  {D : Type v} [Category.{w} D] [HasColimitsOfSize.{w, w} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : K ⥤ SimplexCategory ⥤ C)

/-- 各frameを同じ左随伴で後合成した既存の図式。 -/
abbrev postFrames (L : C ⥤ D) : K ⥤ SimplexCategory ⥤ D :=
  A ⋙ (Functor.whiskeringRight SimplexCategory C D).obj L

/-- 各添字での随伴Hom同型を、標的にも自然に束ねる。 -/
def homPostIso : hom K (postFrames K A L) ≅ R ⋙ hom K A :=
  NatIso.ofComponents (fun Y => NatIso.ofComponents
    (fun k => (adjunctionHomIsoSameUniverse adj (A.obj k.unop)).app Y)
    (by
      intro k l f
      ext n h
      exact adj.homEquiv_naturality_left ((A.map f.unop).app n.unop) h))
    (by
      intro Y Z f
      ext k n h
      exact adj.homEquiv_naturality_right h f)

/-- 指定実現は左随伴の後合成と自然同型で交換する。 -/
def postIso : functor K A ⋙ L ≅ functor K (postFrames K A L) :=
  Adjunction.leftAdjointUniq ((adjunction K A).comp adj)
    ((adjunction K (postFrames K A L)).ofNatIsoRight (homPostIso K adj A))

/-- 交換同型は、両側の指定随伴の単位を保つ。 -/
lemma postIso_unit (W : Kᵒᵖ ⥤ SSet.{w}) :
    ((adjunction K A).comp adj).unit.app W ≫
      (R ⋙ hom K A).map ((postIso K adj A).hom.app W) =
    ((adjunction K (postFrames K A L)).ofNatIsoRight
      (homPostIso K adj A)).unit.app W :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ W

/-- 交換同型の下で、任意の射の指定転置を比較する。 -/
lemma postIso_homEquiv (W : Kᵒᵖ ⥤ SSet.{w}) (Y : D)
    (f : (functor K (postFrames K A L)).obj W ⟶ Y) :
    ((adjunction K A).comp adj).homEquiv W Y ((postIso K adj A).hom.app W ≫ f) =
      (adjunction K (postFrames K A L)).homEquiv W Y f ≫
        (homPostIso K adj A).hom.app Y := by
  rw [Adjunction.homEquiv_naturality_right]
  change ((adjunction K A).comp adj).homEquiv _ _
    ((Adjunction.leftAdjointUniq _ _).hom.app W) ≫ _ = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]
  exact Adjunction.homEquiv_ofNatIsoRight_apply _ _ f

end SerrePositivity.DiagramModel.FrameWeightRealization
