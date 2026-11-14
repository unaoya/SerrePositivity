module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGBimoduleIsoNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGStrictNatTransAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 元の双加群恒等射は、元の厳密 dg 恒等変換へ送られる。 -/
lemma dgBimoduleMapStrictNatTrans_id (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R E C (𝟙 P) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransId (BimoduleCategory.underlying R E C P).toFunctor := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  change _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E C P).obj x))
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E C P).obj x))
      (𝟙 _) = _root_.SerrePositivity.DifferentialGraded.unitElement R _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id (A := R) (D := RightModule R E) _
/-- 元の双加群射の合成は、元の厳密 dg 自然変換の通常順合成へ送られる。 -/
lemma dgBimoduleMapStrictNatTrans_comp {P Q S : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E C}
    (f : P ⟶ Q) (g : Q ⟶ S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R E C (f ≫ g) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R E C f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R E C g) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  apply Subtype.ext
  change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) _ _ (f.val x ≫ g.val x)).val = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp (A := R) (D := RightModule R E) (f.val x) (g.val x)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
