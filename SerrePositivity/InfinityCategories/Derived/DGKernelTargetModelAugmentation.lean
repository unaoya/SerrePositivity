module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleMap
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps
public import SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso
public import SerrePositivity.DifferentialGraded.Tensor.FunctorRestrictionQuasiIso
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphComparison
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory Opposite
variable (R : Type u) [CommRing R] (D C E : Type v)
  [DGCategory R D] [DGCategory R C] [Small.{u} C]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C E)
  (P : BimoduleCategory R E D) (Q : BimoduleCategory R C D)
  (q : Q ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
/-- 指定出力模型の graph 合成から元の kernel への、全 Hom 自然な実比較射。 -/
def dgKernelTargetModelAugmentation :
    BimoduleCategory.of R E D (BimoduleTensor.compose R E C D
      (functorGraph R C E F) (BimoduleCategory.underlying R C D Q)) ⟶ P := by
  let U := BimoduleCategory.of R E C (functorGraph R C E F)
  let a := BimoduleTensor.composeMap R E C D (𝟙 U) q
  let b := BimoduleTensor.middleRestrictionComparisonMap R E E C D F
    (Bimodule.diagonal R E) (BimoduleCategory.underlying R E D P)
  let c := (BimoduleTensor.leftBimoduleUnitIso R E D
    (BimoduleCategory.underlying R E D P)).hom
  exact a ≫ b ≫ c
/-- 比較射の各 tensor 生成元の像は、元の指定随伴転置の像と一致する。 -/
lemma dgKernelTargetModelAugmentation_generator (d : D) (e : E) (c : C) :
    BalancedTensor.ι R C ((BimoduleCategory.underlying R C D Q).rightAt d)
        ((functorGraph R C E F).leftAt e) c ≫
      BimoduleTensor.composeValueMap R E C D
        (𝟙 (BimoduleCategory.of R E C (functorGraph R C E F))) q e d ≫
      BimoduleTensor.middleRestrictionComparisonValue R E E C D F
        (Bimodule.diagonal R E) (BimoduleCategory.underlying R E D P) e d ≫
      (BimoduleTensor.leftUnitValueIso R E D (BimoduleCategory.underlying R E D P) e d).hom =
    BalancedTensor.ι R C ((BimoduleCategory.underlying R C D Q).rightAt d)
        ((functorGraph R C E F).leftAt e) c ≫
      (moduleEvaluation R E e).map (functorExtensionTranspose R C E F (q.val d)) := by
  erw [BimoduleTensor.ι_composeValueMap_assoc]
  have ht := BalancedTensor.ι_functorExtensionTranspose_eval R C E F (q.val d) e c
  apply Eq.trans _ ht.symm
  simp only [BimoduleCategory.valueEvaluation, BimoduleCategory.evaluation,
    CategoryTheory.Functor.comp_map]
  have hm := BimoduleTensor.ι_middleRestrictionComparisonValue R E E C D F
    (Bimodule.diagonal R E) (BimoduleCategory.underlying R E D P) e d c
  have hu := BimoduleTensor.ι_leftUnitValueIso_hom R E D
    (BimoduleCategory.underlying R E D P) e (F.obj c) d
  have hmu := congrArg (fun z => z ≫ (BimoduleTensor.leftUnitValueIso R E D
    (BimoduleCategory.underlying R E D P) e d).hom) hm
  have hc := (Category.assoc _ _ _).symm.trans (hmu.trans hu)
  have hh := congrArg (fun z => ((moduleEvaluation R C c).map (q.val d) ⊗ₘ
    𝟙 (homObject R E e (F.obj c))) ≫ z) hc
  let gid : Bimodule.ClosedMapFamily R E C (functorGraph R C E F) (functorGraph R C E F) :=
    𝟙 (BimoduleCategory.of R E C (functorGraph R C E F))
  have hid : gid.val c =
      𝟙 (ForgetEnrichment.of (Complex R) ((functorGraph R C E F).rightAt c)) := rfl
  rw [hid]
  rw [(moduleEvaluation R E e).map_id
    (ForgetEnrichment.of (Complex R) ((functorGraph R C E F).rightAt c))]
  exact hh
/-- 全 Hom 自然な比較射の各加群成分は、元の指定随伴転置そのもの。 -/
lemma dgKernelTargetModelAugmentation_component (d : D) :
    (BimoduleCategory.evaluation R E D d).map
      (dgKernelTargetModelAugmentation R D C E F P Q q) =
    functorExtensionTranspose R C E F (q.val d) := by
  apply moduleMorphism_ext R E
  intro e
  change (BimoduleCategory.valueEvaluation R E D e d).map
    (dgKernelTargetModelAugmentation R D C E F P Q q) = _
  simp only [dgKernelTargetModelAugmentation, CategoryTheory.Functor.map_comp]
  rw [BimoduleTensor.composeMap_value_eval,
    BimoduleTensor.middleRestrictionComparisonMap_value_eval,
    BimoduleTensor.leftBimoduleUnitIso_hom_value]
  apply BalancedTensor.hom_ext
  intro c
  exact dgKernelTargetModelAugmentation_generator R D C E F P Q q d e c
/-- 準同値と右相対 K-flat な指定模型により、比較射は全評価で準同型。 -/
lemma dgKernelTargetModelAugmentation_quasiIso (hF : QuasiEquivalence F)
    (hQ : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q))
    (hq : BimoduleCategory.quasiIso R C D q) :
    BimoduleCategory.quasiIso R E D
      (dgKernelTargetModelAugmentation R D C E F P Q q) := by
  intro e d
  change QuasiIso ((moduleEvaluation R E e).map
    ((BimoduleCategory.evaluation R E D d).map
      (dgKernelTargetModelAugmentation R D C E F P Q q)))
  rw [dgKernelTargetModelAugmentation_component]
  exact (functorExtensionTranspose_quasiIso R C E F hF (hQ d) (q.val d)
    (fun c => hq c d)) e
end SerrePositivity.InfinityCategories
