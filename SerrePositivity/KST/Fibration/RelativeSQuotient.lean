module
public import SerrePositivity.KST.Fibration.RelativeSConstruction
public import SerrePositivity.KST.Fibration.FullFunctorCore

/-! # 相対 S 構成から商の core への実比較

完全関手の零・押し出し保存を使い、元の全 gapped 図式の後合成を選ぶ。
相対 S_n から商の S_n の core への比較は、その同じ後合成の持ち上げである。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- K-5 の完全関手は K-1/K-2 の S• 保存条件を満たす。 -/
lemma exactMap_preservesSData {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    PreservesSConstructionData q.hom :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q.hom),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare q.hom⟩

/-- wS_n(B) から core S_n(C) への、元の商図式を保つ比較。 -/
def relativeSQuotientMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (relativeSConstruction q.hom n : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C.obj) : SSet.{u}) :=
  relativeDiagramFullFunctorCoreMap q.hom (gappedSubcomplex n B.obj).ι _
    (sPostcomp n q.hom (exactMap_preservesSData q)) rfl

/-- 商比較の包含後は、元の全 gapped 図式への後合成そのもの。 -/
lemma relativeSQuotientMap_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    relativeSQuotientMap q n ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C.obj)).ι =
      (relativeSConstruction q.hom n).ι ≫
        sPostcomp n q.hom (exactMap_preservesSData q) := rfl

/-- 元の core S_n(B) 上で商比較は、元の後合成の core 化を回収する。 -/
lemma relativeSQuotientMap_core {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    relativeDiagramCoreInclusion q.hom (sComponentEvaluation B.obj n) ≫
      relativeSQuotientMap q n =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcomp n q.hom (exactMap_preservesSData q)) :=
  relativeDiagramFullFunctorCoreMap_core q.hom (gappedSubcomplex n B.obj).ι _
    (sPostcomp n q.hom (exactMap_preservesSData q)) rfl

/-- 元の全 gapped 図式の商射は単体作用と厳密に可換。 -/
lemma exactSPostcomp_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) :
    sPostcomp n q.hom (exactMap_preservesSData q) ≫ sMap C.obj θ =
      sMap B.obj θ ≫ sPostcomp m q.hom (exactMap_preservesSData q) := by
  apply (cancel_mono (gappedSubcomplex m C.obj).ι).1
  rw [Category.assoc, sMap_ι]
  change sPostcomp n q.hom (exactMap_preservesSData q) ≫
      (gappedSubcomplex n C.obj).ι ≫ (pre (arNerveMap θ)).app C.obj = _
  change (gappedSubcomplex n B.obj).ι ≫ (ihom (arNerve n)).map q.hom ≫
      (pre (arNerveMap θ)).app C.obj =
    (sMap B.obj θ ≫ (gappedSubcomplex m B.obj).ι) ≫ (ihom (arNerve m)).map q.hom
  rw [sMap_ι, Category.assoc, (pre (arNerveMap θ)).naturality]

/-- 全段の商比較は元の全ての面・退化と可換な自然変換をなす。 -/
def relativeSimplicialQuotientMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    relativeSimplicialSConstruction q.hom ⟶
      simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor where
  app n := relativeSQuotientMap q n.unop.len
  naturality {n m} θ := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction m.unop.len C.obj)).ι).1
    simp only [Category.assoc]
    rw [relativeSQuotientMap_ι]
    change relativeDiagramMap q.hom
        (sComponentEvaluation B.obj n.unop.len) (sComponentEvaluation B.obj m.unop.len)
        (sMap B.obj θ.unop.toOrderHom) (arVertexFunctor.map θ.unop)
        (sComponentEvaluation_reindex B.obj θ) ≫
        (relativeSConstruction q.hom m.unop.len).ι ≫ _ =
      relativeSQuotientMap q n.unop.len ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sMap C.obj θ.unop.toOrderHom) ≫ _
    dsimp only [relativeSConstruction]
    rw [← Category.assoc, relativeDiagramMap_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]
    have he := congrArg (fun a => a ≫ sMap C.obj θ.unop.toOrderHom)
      (relativeSQuotientMap_ι q n.unop.len)
    simp only [Category.assoc] at he ⊢
    rw [he, exactSPostcomp_reindex]
    rfl

end SerrePositivity.KST.Fibration
