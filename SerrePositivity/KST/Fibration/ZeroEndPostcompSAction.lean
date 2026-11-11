module
public import SerrePositivity.KST.Fibration.ZeroEndPostcompFamily
public import SerrePositivity.KST.Fibration.StableZeroSContraction
public import SerrePositivity.KST.Fibration.RelativeSQuotient
public import SerrePositivity.KST.SConstruction.SExactParameterizedNaturality

/-! # 元の零自己関手円柱の零値後合成と、同じ S_n 実円柱の全パラメータ照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の零値後合成円柱を、全自然変換の同じ S_n 作用へ送る。 -/
def zeroEndPostcompSAction {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (n : ℕ) :
    sConstruction n A.obj ⊗ (Δ[1] : SSet.{u}) ⟶ sConstruction n C.obj :=
  uncurry (zeroEndPostcompFamily F hF ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u})).ι ≫ sExactFamilyMap n A C)

/-- 同じ全パラメータの像は、元の S_n 円柱の同じ完全射への後合成そのもの。 -/
theorem zeroEndPostcompSAction_eq {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (n : ℕ) :
    zeroEndPostcompSAction F hF n =
      stableZeroSContractionAction A n ≫ (sExactMap n F).hom := by
  let a := stableZeroEndContractionFamily A
  let b := zeroEndPostcompFamily F hF ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u})).ι
  have hab : ((𝟙 A.obj) ▷ (Δ[1] : SSet.{u})) ≫
      uncurry (b ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C).ι) =
        uncurry (a ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A A).ι) ≫ F.hom := by
    rw [id_whiskerRight, Category.id_comp]
    change uncurry (zeroEndPostcompFamily F hF ≫ stableHomAmbient A C) = _
    rw [zeroEndPostcompFamily_ambient, ← Category.assoc, uncurry_natural_right]
  have hn := sExactParameterizedNaturality n a b (show A ⟶ A from 𝟙 A) F hab
  have hi : (sExactMap n (show A ⟶ A from 𝟙 A)).hom = 𝟙 (sConstruction n A.obj) :=
    sPostcomp_id n A.obj
  rw [hi] at hn
  change (𝟙 (sConstruction n A.obj) ▷ (Δ[1] : SSet.{u})) ≫
    zeroEndPostcompSAction F hF n = stableZeroSContractionAction A n ≫
      (sExactMap n F).hom at hn
  simpa only [id_whiskerRight, Category.id_comp] using hn

/-- 元の零値後合成円柱は、全ての面・退化と同じ全時刻で可換する。 -/
theorem zeroEndPostcompSAction_reindex {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) {m n : ℕ}
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    (sMap A.obj θ ▷ (Δ[1] : SSet.{u})) ≫ zeroEndPostcompSAction F hF m =
      zeroEndPostcompSAction F hF n ≫ sMap C.obj θ := by
  rw [zeroEndPostcompSAction_eq, zeroEndPostcompSAction_eq, ← Category.assoc,
    stableZeroSContractionAction_reindex, Category.assoc]
  exact congrArg (stableZeroSContractionAction A n ≫ ·)
    (exactSPostcomp_reindex F θ).symm

/-- 全 S• の同じ元の実射として保持した零値後合成円柱。 -/
def zeroEndPostcompSNatTrans {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    simplicialSConstruction A.obj ⋙ tensorRight (Δ[1] : SSet.{u}) ⟶
      simplicialSConstruction C.obj where
  app n := zeroEndPostcompSAction F hF n.unop.len
  naturality {_ _} θ := zeroEndPostcompSAction_reindex F hF θ.unop.toOrderHom

/-- 元の全 S• 円柱を、同じ指定完全関手へ全単体で後合成した射と厳密に一致。 -/
theorem zeroEndPostcompSNatTrans_eq {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    zeroEndPostcompSNatTrans F hF = stableZeroSContractionNatTrans A ≫
      simplicialSPostcomp F.hom (exactMap_preservesSData F) := by
  apply NatTrans.ext
  funext n
  exact zeroEndPostcompSAction_eq F hF n.unop.len

end SerrePositivity.KST.Fibration
