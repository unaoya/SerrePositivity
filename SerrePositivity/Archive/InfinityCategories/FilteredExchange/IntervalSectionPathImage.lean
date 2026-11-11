module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalReplacementSectionHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：任意の入力で制限した定値切断収縮の終点像を、同じ入力の元の path へ戻す。
方針：切断と終点の合成の等式を明示し、指定像の一致を前後合成する。
規約：元の指定類を保持。使われ方：共通の左脚の最後の因子の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 切断収縮の制限の終点像は、元の path の同じ制限の指定値になる。 -/
lemma intervalReplacementSectionIso_precomp_endpoint_image {A X Z W : SSet.{u}}
    [KanComplex X] [KanComplex Z] (f : X ⟶ Z)
    (a : A ⟶ intervalReplacement f) (w : Z ⟶ W) :
    HEq ((((intervalReplacementSectionIso f).precomp a).postcomp
      (intervalReplacementEndpoint f)).postcomp w)
      (((intervalReplacementPathIso f).precomp a).postcomp w) := by
  let pr := pullback.snd ((intervalEndpointNatTrans 0).app Z) f
  have hf : pr ≫ f = (pr ≫ intervalReplacementSection f) ≫
      intervalReplacementEndpoint f := by
    rw [Category.assoc, intervalReplacementSection_endpoint]
  have hg : intervalReplacementEndpoint f = (𝟙 _) ≫ intervalReplacementEndpoint f :=
    (Category.id_comp _).symm
  have hp := functorIso_precomp_heq_of_heq (intervalReplacementPathIso f)
    ((intervalReplacementSectionIso f).postcomp (intervalReplacementEndpoint f)) hf hg
    (intervalReplacementSectionIso_endpoint f) a
  rw [functorIso_precomp_postcomp]
  exact functorIso_postcomp_heq_of_heq ((intervalReplacementPathIso f).precomp a)
    (((intervalReplacementSectionIso f).postcomp (intervalReplacementEndpoint f)).precomp a)
    (congrArg (fun k => a ≫ k) hf) (congrArg (fun k => a ≫ k) hg) hp w

end SerrePositivity.InfinityCategories.F2
