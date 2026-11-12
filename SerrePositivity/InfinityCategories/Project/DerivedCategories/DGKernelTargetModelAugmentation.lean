module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Tensor.ResolvedRestriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelSourceGraphComparison
/-!
概要：出力模型の graph 合成から元の kernel への実比較射と準同型性を構成する。
方針：全 Hom 自然な中間制限比較と単位子を合成し、同じ随伴転置の生成元の式と照合する。
規約：元の kernel の射影性・平坦性を仮定しない。指定模型の右相対 K-flat 性だけを使う。
使われ方：一般 kernel の出力模型移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory Opposite
variable (R : Type u) [CommRing R] (D C E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D)
  (q : Q ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
/-- 指定出力模型の graph 合成から元の kernel への、全 Hom 自然な実比較射。 -/
def dgKernelTargetModelAugmentation :
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E C D
      (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q)) ⟶ P := by
  let U := _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F)
  let a := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E C D (𝟙 U) q
  let b := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.middleRestrictionComparisonMap R E E C D F
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R E) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)
  let c := (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R E D
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)).hom
  exact a ≫ b ≫ c
/-- 比較射の各 tensor 生成元の像は、元の指定随伴転置の像と一致する。 -/
lemma dgKernelTargetModelAugmentation_generator (d : D) (e : E) (c : C) :
    _root_.SerrePositivity.DifferentialGraded.BalancedTensor.ι R C ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q).rightAt d)
        ((_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F).leftAt e) c ≫
      _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueMap R E C D
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))) q e d ≫
      _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.middleRestrictionComparisonValue R E E C D F
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R E) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) e d ≫
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftUnitValueIso R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) e d).hom =
    _root_.SerrePositivity.DifferentialGraded.BalancedTensor.ι R C ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q).rightAt d)
        ((_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F).leftAt e) c ≫
      (_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R E e).map (_root_.SerrePositivity.DifferentialGraded.functorExtensionTranspose R C E F (q.val d)) := by
  erw [_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.ι_composeValueMap_assoc]
  have ht := _root_.SerrePositivity.DifferentialGraded.BalancedTensor.ι_functorExtensionTranspose_eval R C E F (q.val d) e c
  apply Eq.trans _ ht.symm
  simp only [_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation,
    CategoryTheory.Functor.comp_map]
  have hm := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.ι_middleRestrictionComparisonValue R E E C D F
    (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R E) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) e d c
  have hu := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.ι_leftUnitValueIso_hom R E D
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) e (F.obj c) d
  have hmu := congrArg (fun z => z ≫ (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftUnitValueIso R E D
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) e d).hom) hm
  have hc := (Category.assoc _ _ _).symm.trans (hmu.trans hu)
  have hh := congrArg (fun z => ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R C c).map (q.val d) ⊗ₘ
    𝟙 (_root_.SerrePositivity.DifferentialGraded.homObject R E e (F.obj c))) ≫ z) hc
  let gid : _root_.SerrePositivity.DifferentialGraded.Bimodule.ClosedMapFamily R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F) (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F) :=
    𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))
  have hid : gid.val c =
      𝟙 (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) ((_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F).rightAt c)) := rfl
  rw [hid]
  rw [(_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R E e).map_id
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) ((_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F).rightAt c))]
  exact hh
/-- 全 Hom 自然な比較射の各加群成分は、元の指定随伴転置そのもの。 -/
lemma dgKernelTargetModelAugmentation_component (d : D) :
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R E D d).map
      (dgKernelTargetModelAugmentation R D C E F P Q q) =
    _root_.SerrePositivity.DifferentialGraded.functorExtensionTranspose R C E F (q.val d) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext R E
  intro e
  change (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R E D e d).map
    (dgKernelTargetModelAugmentation R D C E F P Q q) = _
  simp only [dgKernelTargetModelAugmentation, CategoryTheory.Functor.map_comp]
  rw [_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_value_eval,
    _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.middleRestrictionComparisonMap_value_eval,
    _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso_hom_value]
  apply _root_.SerrePositivity.DifferentialGraded.BalancedTensor.hom_ext
  intro c
  exact dgKernelTargetModelAugmentation_generator R D C E F P Q q d e c
/-- 準同値と右相対 K-flat な指定模型により、比較射は全評価で準同型。 -/
lemma dgKernelTargetModelAugmentation_quasiIso (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q))
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q) :
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D
      (dgKernelTargetModelAugmentation R D C E F P Q q) := by
  intro e d
  change QuasiIso ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R E e).map
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R E D d).map
      (dgKernelTargetModelAugmentation R D C E F P Q q)))
  rw [dgKernelTargetModelAugmentation_component]
  exact (_root_.SerrePositivity.DifferentialGraded.functorExtensionTranspose_quasiIso R C E F hF (hQ d) (q.val d)
    (fun c => hq c d)) e
end SerrePositivity.InfinityCategories.Project.DerivedCategories
