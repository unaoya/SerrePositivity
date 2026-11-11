module
public import SerrePositivity.KST.SConstruction.PointwiseCofiberPushout
public import SerrePositivity.KST.SConstruction.PointwiseGappedPushout
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexFunctorFaithful

/-! # cofiber 値の点ごとの押し出しと gapped 性
概要：cofiber 値に持ち上げた元の押し出しの族は、入力が gapped なら gapped。
方針：cofiber 包含の充満忠実性で関手同型を持ち上げる。
規約：元の C 内の選択を保持する。使われ方：McCarthy の ρ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：cofiber 図式内の押し出しと元の C 内の押し出しの持ち上げは関手として同型。
方針：包含後の比較同型を関手圏の充満忠実性で戻す。
規約：全パラメーターの同型。使われ方：gapped 条件の輸送。 -/
def pointwiseCofiberPushout_iso {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ cofiberDiagrams C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pointwisePushoutApex (curry F)) (pointwiseCofiberPushout F) := by
  let e := pointwiseDiagramPushoutApex_postcompIso F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι
      (cofiberInclusion_preservesSConstructionData C)
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.fullSubcomplexFunctorInclusionHoFullyFaithful K
    ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) IsCofiberDiagramVertex).preimageIso e

/-- 概要：gapped な cofiber 図式の span の元の C 内の押し出しも gapped。
方針：cofiber 図式内の押し出しの gapped 性を関手同型で移す。
規約：gapped 条件は入力 span の三頂点で要求する。使われ方：raw ρ の gapped 性。 -/
lemma pointwiseCofiberPushout_isGapped {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ arNerve n ⟶ cofiberDiagrams C)
    (hg : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, IsGapped
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (horn 2 0) (cofiberDiagrams C) (curry F)).app
          (Opposite.op ⦋0⦌) a))) : IsGapped (pointwiseCofiberPushout F) :=
  (pointwisePushoutApex_isGapped F hg).of_functorIso (pointwiseCofiberPushout_iso F)

end SerrePositivity.KST.SConstruction
