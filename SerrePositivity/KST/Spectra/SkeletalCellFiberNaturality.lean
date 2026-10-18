module

public import SerrePositivity.KST.Spectra.UnbasedRestrictionFiberNaturality
public import SerrePositivity.KST.Spectra.SkeletalFiberDifferentialNaturality
public import SerrePositivity.KST.Spectra.SkeletalCellCofiber

/-!
概要：骨格の相対 cofiber とセルの cofiber の Hom の fiber 表示の自然性。
方針：制限の fiber 表示の自然性に、源の同型への前合成の自然性を合成する。
規約：係数の Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。セルの群の係数自然性への入力。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace UnbasedPointedMapping

/-- 概要：相対骨格の Hom による実際の fiber の表示は係数射に自然。
方針：一般の制限の cofiber 表示の自然性を隣接骨格の包含へ適用する。
規約：元の fiber は塔の実際の遷移の fiber。
使われ方：Goerss–Jardine VIII §1。fiber の群の係数表示の比較。 -/
@[reassoc]
lemma stageFiberIso_natural (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}}
    (p : Y ⟶ Z) (n : ℕ) :
    PointedObject.basedHomMap (skeletalRelativeSource K n) (Y := Y) (Z := Z) p ≫
        (stageFiberIso K Z n).hom =
      (stageFiberIso K Y n).hom ≫ stageFiberMap K (Y := Y) (Z := Z) p n := by
  exact restrictionFiberIso_natural (skeletalInclusion K n) p

end UnbasedPointedMapping

namespace SkeletalCellAttachment

/-- 概要：セルの cofiber の Hom から実際の骨格の fiber への同型は係数射に自然。
方針：相対 cofiber の同型への前合成と fiber の比較の自然性を合成する。
規約：この比較は厳密な点つき同型の式。
使われ方：Goerss–Jardine VIII §1。非退化セルの係数の関数表示の自然性。 -/
@[reassoc]
lemma stageFiberCellIso_natural (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}}
    (p : Y ⟶ Z) (n : ℕ) :
    PointedObject.basedHomMap (cellCofiber K (n + 1)) (Y := Y) (Z := Z) p ≫
        (stageFiberCellIso K Z n).hom =
      (stageFiberCellIso K Y n).hom ≫
        UnbasedPointedMapping.stageFiberMap K (Y := Y) (Z := Z) p n := by
  have hs : PointedObject.basedHomMap (cellCofiber K (n + 1)) (Y := Y) (Z := Z) p ≫
      (MonoidalClosed.pre (relativeCofiberIso K (n + 1)).hom).app Z =
    (MonoidalClosed.pre (relativeCofiberIso K (n + 1)).hom).app Y ≫
      PointedObject.basedHomMap (UnbasedPointedMapping.skeletalRelativeSource K n)
        (Y := Y) (Z := Z) p :=
    (MonoidalClosed.pre (relativeCofiberIso K (n + 1)).hom).naturality p
  have ht := UnbasedPointedMapping.stageFiberIso_natural K p n
  change _ ≫ ((MonoidalClosed.pre (relativeCofiberIso K (n + 1)).hom).app Z ≫ _) =
    ((MonoidalClosed.pre (relativeCofiberIso K (n + 1)).hom).app Y ≫ _) ≫ _
  erw [← Category.assoc, hs, Category.assoc, ht, ← Category.assoc]

end SkeletalCellAttachment

end

end SerrePositivity.KST.Spectra
