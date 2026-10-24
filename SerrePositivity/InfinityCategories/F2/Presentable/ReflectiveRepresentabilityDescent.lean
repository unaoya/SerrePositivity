module

public import SerrePositivity.InfinityCategories.F2.Presentable.RepresentabilityEquivalence
public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveLocalObjects

/-!
概要：反映模型で得られた局所な表現対象を元の反映部分圏へ降ろす。
方針：局所対象の本質的像表示と元の全 Hom 比較を使い、余単位で前層を回収する。
規約：反映と局所性は明示し、局所対象の存在自体はこの補題で仮定へ隠さない。
使われ方：一般の presentable 圏の表現可能性の下降部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：反映へ引き戻した前層の表現対象が局所なら元の前層は表現可能。
方針：表現対象を包含の像へ移し、充満忠実な制限と指定余単位で全自然同型を回収する。
規約：局所性の証明を別工程とし、元の前層の表現同型は結論として構成する。
使われ方：前層圏での構成から反映された presentable 圏への移送。 -/
lemma reflective_isRepresentable_of_local_representation
    {X : SSet.{u + 1}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
    (r : ReflectiveSubcategory X P)
    (F : (fullSubcomplexOnVertices X P : SSet.{u + 1}).op ⟶ SpaceInfinity.{u})
    (z : X _⦋0⦌) (hz : r.IsLocal z)
    (h : FunctorIso (representablePresheafInfinity z)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map r.reflector ≫ F) ≫
        Compact.spaceUniverseDiagram)) : IsRepresentableSmallSpaceFunctor F := by
  obtain ⟨y, ⟨ey⟩⟩ := (r.isLocal_iff_essentialImage z).mp hz
  have hr := isRepresentable_restriction_of_essentialImage
    (fullSubcomplexOnVertices X P).ι r.inclusion_fullyFaithful
    (SSet.opFunctor.map r.reflector ≫ F) y z ey h
  apply hr.of_functorIso
  have he := FunctorIso.postcomp r.counitIso.op F
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc] using he

end SerrePositivity.InfinityCategories.F2.Presentable
