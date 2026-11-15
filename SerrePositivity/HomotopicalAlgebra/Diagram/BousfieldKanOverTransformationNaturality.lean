module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanOverTransformation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyNaturality

/-!
概要：指定変換のOverへの移送のnerveホモトピーは添字に自然。
方針：Overの関手の等式と成分の一致を先に示し、nerveのwhisker法則を使う。
使われ方：HTT 4.2.4.4、RR02(a)の指定余単位による実現の円柱。
規約：元の指定変換を保持し、自然性を仮定として追加しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory MonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.DiagramModel.FrameWeightRealization

/-- 関手の等式で端点を揃えた同じ自然変換は、同じnerve円柱を与える。 -/
lemma nerveTransformationCylinder_congr {C D : Type w} [SmallCategory C] [SmallCategory D]
    {F F' G G' : C ⥤ D} (η : F ⟶ G) (η' : F' ⟶ G')
    (hF : F = F') (hG : G = G')
    (hη : η ≫ eqToHom hG = eqToHom hF ≫ η') :
    (nerveNatTransHomotopy η).h = (nerveNatTransHomotopy η').h := by
  subst F'
  subst G'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hη
  subst η'
  rfl

variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {P Q : L ⥤ K} (α : P ⟶ Q) {i j : L} (f : i ⟶ j)

lemma overTransformationSource_map :
    Over.map f.op ⋙ overTransformationSource α i =
      overTransformationSource α j ⋙ Over.map (P.map f).op := by
  refine CategoryTheory.Functor.ext (fun a => ?_) ?_
  · change Over.mk (Q.op.map (a.hom ≫ f.op) ≫ (α.app i).op) =
      Over.mk ((Q.op.map a.hom ≫ (α.app j).op) ≫ (P.map f).op)
    have h : Q.op.map f.op ≫ (α.app i).op = (α.app j).op ≫ (P.map f).op := by
      apply Quiver.Hom.unop_inj
      exact (α.naturality f).symm
    simp only [Q.op.map_comp, Category.assoc, h]
  · intro a b g
    apply Over.OverMorphism.ext
    simp [overTransformationSource, Over.eqToHom_left]

/-- 同じ添字の射で前合成した円柱と、像で後合成した円柱は一致する。 -/
lemma overTransformationHomotopy_naturality :
    (nerveMap (Over.map f.op) ▷ (Δ[1] : SSet.{w})) ≫
        (overTransformationHomotopy α i).h =
      (overTransformationHomotopy α j).h ≫ nerveMap (Over.map (P.map f).op) := by
  change (nerveMap (Over.map f.op) ▷ (Δ[1] : SSet.{w})) ≫
      (nerveNatTransHomotopy (overTransformation α i)).h =
    (nerveNatTransHomotopy (overTransformation α j)).h ≫
      nerveMap (Over.map (P.map f).op)
  rw [nerveNatTransHomotopy_whiskerLeft, nerveNatTransHomotopy_whiskerRight]
  apply nerveTransformationCylinder_congr _ _ (overTransformationSource_map α f)
    (overPost_map_eq P.op f.op)
  apply NatTrans.ext
  funext a
  apply Over.OverMorphism.ext
  simp [overTransformation, Over.eqToHom_left]

end SerrePositivity.DiagramModel.FrameWeightRealization
