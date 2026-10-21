module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerve
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransAlgebra
public import SerrePositivity.InfinityCategories.DGNerve.ClosedComposition
/-!
概要：元の双加群射を同じ厳密 dg 自然変換へ送る操作は、恒等と合成を保つ。
方針：元の全閉零成分と全 Hom 自然性、実 nerve 写像と端点輸送を使う。
規約：関手圏の射の等式を実単体で証明する。使われ方：kernel 比較の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (C : Type (max (u + 1) v)) [DGCategory R C]
/-- 元の双加群恒等射は、元の厳密 dg 恒等変換へ送られる。 -/
lemma dgBimoduleMapStrictNatTrans_id (P : BimoduleCategory R E C) :
    dgBimoduleMapStrictNatTrans R E C (𝟙 P) =
      dgStrictNatTransId (BimoduleCategory.underlying R E C P).toFunctor := by
  apply dgStrictNatTrans_ext
  intro x
  change closedHomEquiv R (RightModule R E)
      (ForgetEnrichment.of (Complex R) ((BimoduleCategory.underlying R E C P).obj x))
      (ForgetEnrichment.of (Complex R) ((BimoduleCategory.underlying R E C P).obj x))
      (𝟙 _) = unitElement R _
  exact closedHom_id (A := R) (D := RightModule R E) _
/-- 元の双加群射の合成は、元の厳密 dg 自然変換の通常順合成へ送られる。 -/
lemma dgBimoduleMapStrictNatTrans_comp {P Q S : BimoduleCategory R E C}
    (f : P ⟶ Q) (g : Q ⟶ S) :
    dgBimoduleMapStrictNatTrans R E C (f ≫ g) =
      dgStrictNatTransComp (dgBimoduleMapStrictNatTrans R E C f)
        (dgBimoduleMapStrictNatTrans R E C g) := by
  apply dgStrictNatTrans_ext
  intro x
  apply Subtype.ext
  change (closedHomEquiv R (RightModule R E) _ _ (f.val x ≫ g.val x)).val = _
  exact closedHom_comp (A := R) (D := RightModule R E) (f.val x) (g.val x)
end SerrePositivity.InfinityCategories
