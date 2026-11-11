module
public import SerrePositivity.KST.Fibration.RelativeSQuotient
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-! # K-6 の元の Ar 評価・S 後合成の完全性と零対象検出

固定 K-1/K-2 の包含・全 Ar 評価・cofiber 保存を使う。
新たな S• 模型や一般安定圏上の K は導入しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の全 Ar 成分評価は、零対象と同じ実 cofiber 正方形を保存する。 -/
instance sComponentEvaluation_isExactFunctor (B : SSet.{u}) [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable B]
    (n : ℕ) (a : (arNerve n) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (sComponentEvaluation B n a) where
  preservesZero _ hv := isZeroVertex_evaluateFunctorAt (gappedInclusion_isZeroVertex n hv) a
  preservesCofiber t ht := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ sComponentEvaluation B n a)
    simpa only [sComponentEvaluation, Category.assoc] using
      (gappedInclusion_cofiber_iff_pointwise t).mp ht a

/-- 元の相対商比較が使う同じ S 後合成は完全関手。 -/
instance exactSPostcomp_isExactFunctor {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (sPostcomp n q.hom (exactMap_preservesSData q)) where
  preservesZero _ hv := sPostcomp_isZeroVertex n q.hom (exactMap_preservesSData q) hv
  preservesCofiber t ht := sPostcomp_preserves_cofiber q.hom (exactMap_preservesSData q) t ht

/-- 零対象を保つ充満忠実な実関手は、元の零対象の存在を用いて零性を反映する。 -/
theorem zeroVertex_of_fullyFaithful_preservesZero {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [Quasicategory Y] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) (hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices f) {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (f.app (Opposite.op ⦋0⦌) x)) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroVertexIso ⟨_, (hzero z.vertex z.isZero).1, (hzero z.vertex z.isZero).2⟩
    ⟨_, hx.1, hx.2⟩
  exact z.isZero.of_vertexIso (hf.preimageVertexIso e)

/-- 元の全 gapped 図式が零対象であることは、全 Ar 成分の零性と同値。 -/
theorem sConstruction_isZeroVertex_iff_components (B : SSet.{u})
    [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable B] (n : ℕ) (v : (sConstruction n B) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v ↔ ∀ a : (arNerve n) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sComponentEvaluation B n a).app (Opposite.op ⦋0⦌) v) := by
  constructor
  · intro hv a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := sComponentEvaluation B n a) _ hv
  · intro hv
    apply zeroVertex_of_fullyFaithful_preservesZero (X := sConstruction n B)
      (Y := (ihom (arNerve n)).obj B)
      (gappedSubcomplex n B).ι
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _)
      (fun _ hz => gappedInclusion_isZeroVertex n hz)
    exact isZeroVertex_of_pointwise ((gappedSubcomplex n B).ι.app (Opposite.op ⦋0⦌) v) hv

end SerrePositivity.KST.Fibration
