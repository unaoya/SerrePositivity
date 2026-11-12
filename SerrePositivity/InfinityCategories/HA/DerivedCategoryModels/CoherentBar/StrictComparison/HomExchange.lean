module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
概要：閉零射による全次数 Hom の前後合成と微分の可換式を成分で公開する。
方針：既存の enriched Hom 関手の可換式を同じ次数で評価する。
規約：dg 加群の主 Hom end を使う。
使われ方：augmentation の正規化への移送と局所縮約の閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgStrictHom_whisker_exchange {M' M N N' : ModuleCategory R D}
    (i : M' ⟶ M) (p : N ⟶ N') (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X q) :
    (eHomWhiskerRight (Complex R) i N').f q
        ((eHomWhiskerLeft (Complex R) M p).f q z) =
      (eHomWhiskerLeft (Complex R) M' p).f q
        ((eHomWhiskerRight (Complex R) i N).f q z) :=
  congrArg (fun f => f.f q z) (eHom_whisker_exchange (Complex R) i p)

lemma dgStrictHom_postcompose_d {M N P : ModuleCategory R D} (p : N ⟶ P) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X q) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) P)).d q (q + 1)
      ((eHomWhiskerLeft (Complex R) M p).f q z) =
    (eHomWhiskerLeft (Complex R) M p).f (q + 1)
      ((moduleHom R D (ForgetEnrichment.to (Complex R) M)
        (ForgetEnrichment.to (Complex R) N)).d q (q + 1) z) :=
  ConcreteCategory.congr_hom ((eHomWhiskerLeft (Complex R) M p).comm q (q + 1)) z

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
