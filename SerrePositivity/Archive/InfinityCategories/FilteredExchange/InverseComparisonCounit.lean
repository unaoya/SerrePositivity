module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPrecompFaithful
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoSelfUnitExchange

/-!
概要：指定単位から作る逆比較の余単位を、同じ指定単位の三角恒等式で検証する。
方針：元の逆関手による前合成の忠実性と、指定同型の交換則を使う。
規約：単位と既存の逆比較を選び直さない。使われ方：pointed 値比較の指定因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の逆比較と指定単位から構成した、同じ逆射の余単位。 -/
def inverseComparisonCounit {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y)
    (r : Y ⟶ X) (u : FunctorIso (e.hom ≫ r) (𝟙 X)) :
    FunctorIso (r ≫ e.hom) (𝟙 Y) := by
  have hi : FunctorIso e.inv r := by
    have a := (u.precomp e.inv).symm
    have b := e.invHomIso.postcomp r
    have b' : FunctorIso (e.inv ≫ e.hom ≫ r) r := by
      simpa only [Category.assoc, Category.id_comp] using b
    have a' : FunctorIso e.inv (e.inv ≫ e.hom ≫ r) := by
      simpa only [Category.assoc, Category.comp_id] using a
    exact a' ≪≫ b'
  exact (hi.postcomp e.hom).symm ≪≫ e.invHomIso

/-- 同じ単位で構成した余単位は、元の同じ関手上の三角恒等式を満たす。 -/
lemma inverseComparisonCounit_triangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y)
    (r : Y ⟶ X) (u : FunctorIso (e.hom ≫ r) (𝟙 X)) :
    u.postcomp e.hom = (inverseComparisonCounit e r u).precomp e.hom := by
  let c := inverseComparisonCounit e r u
  have hid := functorIso_precomp_id c
  have hx := functorIso_whisker_exchange e.invHomIso c
  rw [hid, functorIso_postcomp_id] at hx
  have hl : e.invHomIso.postcomp (r ≫ e.hom) ≪≫ c =
      (u.precomp e.inv).postcomp e.hom ≪≫ e.invHomIso := by
    change e.invHomIso.postcomp (r ≫ e.hom) ≪≫
      ((FunctorIso.postcomp ((u.precomp e.inv).symm ≪≫ e.invHomIso.postcomp r) e.hom).symm ≪≫
        e.invHomIso) = _
    rw [functorIso_postcomp_trans, functorIso_postcomp_symm]
    simp only [Iso.trans_symm, Iso.symm_symm_eq, ← functorIso_postcomp_postcomp]
    simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  have hc := congrArg (fun k => k ≪≫ e.invHomIso.symm) (hl.symm.trans hx)
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] at hc
  apply functorIso_precomp_injective_of_qCatEquivalence e.inv e.symm.isQCatEquivalence
  change (u.postcomp e.hom).precomp e.inv = (c.precomp e.hom).precomp e.inv
  rw [← functorIso_precomp_postcomp, functorIso_precomp_precomp]
  exact hc

end SerrePositivity.InfinityCategories.F2
