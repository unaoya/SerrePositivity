module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionShapePushout
public import Mathlib.CategoryTheory.Limits.Over

/-!
概要：任意の通常の形状の余極限に沿って、底を固定する切断の全パラメータの族を貼る。
方針：底上の余極限を忘却して直積を取り、展開した族を余極限の普遍性で貼り合わせる。
規約：貼り合わせの一意性は高次パラメータを含む。局所 Kan 性を要求しない。
使われ方：一般の coherent な図式の骨格・セルの余積・極限段階での切断の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E S T : SSet.{u}} (q : E ⟶ S)
  {J : Type w} [SmallCategory J] (F : J ⥤ Over S)

/-- 底上の図式の余錐は、相対関手空間の反変図式の錐を与える。 -/
def relativeFunctorOverColimitCone (c : Cocone F) :
    Cone (F.op ⋙ relativeFunctorOverFunctor q) where
  pt := relativeFunctorSpace q c.pt.hom
  π :=
    { app j := relativeFunctorOverPre q (c.ι.app j.unop)
      naturality := by
        intro a b f
        change 𝟙 _ ≫ relativeFunctorOverPre q (c.ι.app b.unop) =
          relativeFunctorOverPre q (c.ι.app a.unop) ≫ relativeFunctorOverPre q (F.map f.unop)
        rw [Category.id_comp, ← relativeFunctorOverPre_comp, c.w f.unop] }

/-- 底上の余極限に沿う相対関手の族は、各部分上の整合する族から唯一に決まる。 -/
lemma relativeFunctorOver_colimit_lift (c : Cocone F) (hc : IsColimit c)
    (s : Cone (F.op ⋙ relativeFunctorOverFunctor q)) :
    ∃! t : s.pt ⟶ relativeFunctorSpace q c.pt.hom,
      ∀ j : Jᵒᵖ, t ≫ relativeFunctorOverPre q (c.ι.app j.unop) = s.π.app j := by
  let c₀ := (Over.forget S).mapCocone c
  let cT := (tensorRight s.pt).mapCocone c₀
  let hc₀ := isColimitOfPreserves (Over.forget S) hc
  let hcT := isColimitOfPreserves (tensorRight s.pt) hc₀
  let d : Cocone (F ⋙ Over.forget S ⋙ tensorRight s.pt) :=
    { pt := E
      ι :=
        { app j := relativeFunctorUncurry (s.π.app (Opposite.op j))
          naturality := by
            intro a b f
            change ((F.map f).left ▷ s.pt) ≫
              relativeFunctorUncurry (s.π.app (Opposite.op b)) =
                relativeFunctorUncurry (s.π.app (Opposite.op a))
            rw [← relativeFunctorOverPre_uncurry]
            exact congrArg relativeFunctorUncurry (s.w f.op) } }
  let H := hcT.desc d
  have hH : H ≫ q = fst c.pt.left s.pt ≫ c.pt.hom := by
    apply hcT.hom_ext
    intro j
    rw [← Category.assoc, hcT.fac d j, relativeFunctorUncurry_projection]
    change fst (F.obj j).left s.pt ≫ (F.obj j).hom =
      ((c.ι.app j).left ▷ s.pt) ≫ fst c.pt.left s.pt ≫ c.pt.hom
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]
    exact congrArg (fun h ↦ fst (F.obj j).left s.pt ≫ h) (c.ι.app j).w.symm
  let t := relativeFunctorCurry H hH
  have ht : relativeFunctorUncurry t = H := relativeFunctorUncurry_curry _ _
  refine ⟨t, ?_, ?_⟩
  · intro j
    apply relativeFunctorUncurry_injective q (F.obj j.unop).hom
    rw [relativeFunctorOverPre_uncurry, ht]
    exact hcT.fac d j.unop
  · intro m hm
    apply relativeFunctorUncurry_injective q c.pt.hom
    rw [ht]
    apply hcT.hom_ext
    intro j
    change ((c.ι.app j).left ▷ s.pt) ≫ relativeFunctorUncurry m =
      ((c.ι.app j).left ▷ s.pt) ≫ H
    rw [← relativeFunctorOverPre_uncurry, hm]
    exact (hcT.fac d j).symm

/-- 底上の余極限に対する切断空間は、各部分の切断空間の実際の極限である。 -/
def relativeFunctorOverColimitCone_isLimit (c : Cocone F) (hc : IsColimit c) :
    IsLimit (relativeFunctorOverColimitCone q F c) where
  lift s := (relativeFunctorOver_colimit_lift q F c hc s).choose
  fac s j := (relativeFunctorOver_colimit_lift q F c hc s).choose_spec.1 j
  uniq s m hm := (relativeFunctorOver_colimit_lift q F c hc s).choose_spec.2 m hm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
