module

public import SerrePositivity.KST.LocalizingInvariants.DGExtensionUnitHomNaturality
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements

/-!
概要：D の元の graph 延長・制限の余単位の全 Hom 自然性を供給する。
方針：純粋生成元への制限 Hom の作用と、D の全次数 Yoneda 評価自然性を使う。
規約：元の tensor 延長と評価を保持。使われ方：実 Perf 合成比較の厳密 dg 自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

lemma dgExtensionCounitHomNaturality_eval (M N : RightModule R E) (e : E) :
    (moduleRestrictionHom R D E F.op M N ≫ BalancedTensor.rightHomMap R D _ _
      ((functorGraph R D E F).leftAt e)) ≫ homPostcompose _
        (functorExtensionEvaluationComponent R D E F N e) =
      moduleHomπ R E M N e ≫ homPrecompose
        (functorExtensionEvaluationComponent R D E F M e) _ := by
  apply BalancedTensor.homMap_post_pre_eq
  intro k z d r s a n ha hn m h
  change (functorExtensionEvaluationComponent R D E F N e).f n
      (((BalancedTensor.rightHomMap R D _ _ ((functorGraph R D E F).leftAt e)).f k
        ((moduleRestrictionHom R D E F.op M N).f k z)).v a n hn
        (BalancedTensor.element R D _ _ d m h ha)) = _
  have hp := congrArg (fun q => q.f k z) (moduleRestrictionHom_π R D E F.op M N d)
  change (moduleHomπ R D _ _ d).f k ((moduleRestrictionHom R D E F.op M N).f k z) =
    (moduleHomπ R E M N (F.obj d)).f k z at hp
  have ht := BalancedTensor.rightHomMap_element_of_sum R D
    ((functorGraph R D E F).leftAt e) ((moduleRestrictionHom R D E F.op M N).f k z)
    d m h ha (rfl : k + r = k + r) hn
  rw [hp] at ht
  have hc := congrArg (fun x => (functorExtensionEvaluationComponent R D E F N e).f n x) ht
  refine hc.trans ?_
  let h' : GradedHom R e (F.obj d) s := h
  let zm := ((moduleHomπ R E M N (F.obj d)).f k z).v r (k + r) (by omega) m
  have hN := functorExtensionEvaluation_element R D E F N e d zm h' (by omega : k + r + s = n)
  have hM := functorExtensionEvaluation_element R D E F M e d m h' ha
  have hy := BalancedTensor.leftYonedaEvaluation_homElement R E z e (F.obj d) m h'
    ha (by omega : r + k = k + r) hn
  simp only [BalancedTensor.leftYonedaEvaluation_element] at hy
  exact hN.trans (hy.symm.trans (congrArg
    (fun x => ((moduleHomπ R E M N e).f k z).v a n hn x) hM.symm))

lemma dgExtensionCounitHomNaturality (M N : RightModule R E) :
    (moduleRestrictionHom R D E F.op M N ≫ (dgModuleExtension R D E F).map _ _) ≫
      moduleHomPostcompose R E _ _ _ (functorExtensionCounit R D E F N) =
        moduleHomPrecompose R E _ _ _ (functorExtensionCounit R D E F M) := by
  apply moduleHom_ext
  intro e
  calc
    _ = ((moduleRestrictionHom R D E F.op M N ≫
        ((dgModuleExtension R D E F).map _ _ ≫ moduleHomπ R E _ _ e)) ≫
          homPostcompose _ (functorExtensionEvaluationComponent R D E F N e)) := by
      simp only [Category.assoc, moduleHomPostcompose_π, moduleMorphismComponent,
        functorExtensionCounit_eval]
    _ = (moduleRestrictionHom R D E F.op M N ≫ BalancedTensor.rightHomMap R D _ _
        ((functorGraph R D E F).leftAt e)) ≫ homPostcompose _
          (functorExtensionEvaluationComponent R D E F N e) := by
      rw [dgModuleExtension_map_π]
      rfl
    _ = moduleHomπ R E M N e ≫ homPrecompose
        (functorExtensionEvaluationComponent R D E F M e) _ :=
      dgExtensionCounitHomNaturality_eval R D E F M N e
    _ = _ := by
      rw [moduleHomPrecompose_π]
      change _ = _ ≫ homPrecompose ((moduleEvaluation R E e).map
        (functorExtensionCounit R D E F M)) _
      rw [functorExtensionCounit_eval]

/-- 元の余単位射を全成分に持つ厳密 dg 自然変換。 -/
def dgExtensionCounitStrict : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
    ((dgModuleRestriction R D E F.op).comp (dgModuleExtension R D E F))
    (DGFunctor.id (RightModule R E)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R E
    (fun M => functorExtensionCounit R D E F M) (fun M N => by
      change _ = 𝟙 _ ≫ _
      rw [Category.id_comp]
      exact dgExtensionCounitHomNaturality R D E F M N)

end SerrePositivity.KST.LocalizingInvariants
