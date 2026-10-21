module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInfinity
/-!
概要：元の同じ入力から元の半自由模型への実 ∞ 関手を、指定比較射に沿って比較する。
方針：同じ分解変更の全関手同型へ、元の対象宇宙の上げ下げを前後合成する。
規約：元の出力の射影性を要求しない。使われ方：任意双加群の実導来作用の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
    (ForgetEnrichment.of (Complex R) (G.obj y)))
/-- 全 Hom 自然な次数別全射準同型に沿う、元の実半自由出力 ∞ 関手の全関手同型。 -/
def dgModuleResolvedInfinity_changeIso :
    FunctorIso (dgModuleResolvedInfinity R C E F) (dgModuleResolvedInfinity R C E G) := by
  have e := ((dgModuleOutputResolution_changeIso R C E a hs hq ha).precomp
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).postcomp
      (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (SemifreeDGModules R E)))
  simpa only [dgModuleResolvedInfinity, Category.assoc] using e
end SerrePositivity.InfinityCategories
