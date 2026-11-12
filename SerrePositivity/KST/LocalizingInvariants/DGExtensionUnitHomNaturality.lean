module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTrans
public import SerrePositivity.DifferentialGraded.Module.Functor
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-!
概要：D の元の graph 延長・制限の単位が、全 Hom 複体について自然であることを示す。
方針：元の tensor 挿入と斉次射の作用を純粋生成元で比較する。
規約：D の延長・加群模型をそのまま使う。使われ方：Perf の値の塔の合成比較。
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

lemma dgExtensionUnitHomNaturality_eval (M N : RightModule R D) (d : D) :
    moduleHomπ R D M N d ≫ homPostcompose (M.obj (op d))
      (functorExtensionInsertionComponent R D E F N d) =
    ((dgModuleExtension R D E F).map M N ≫ moduleHomπ R E _ _ (F.obj d)) ≫
      homPrecompose (functorExtensionInsertionComponent R D E F M d) _ := by
  rw [dgModuleExtension_map_π]
  apply hom_naturality_of_apply
  intro k z
  ext i j hij m
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply]
  have hN := functorExtensionInsertion_apply R D E F N d j
    (((moduleHomπ R D M N d).f k z).v i j hij m)
  have hM := functorExtensionInsertion_apply R D E F M d i m
  have he := BalancedTensor.rightHomMap_element_of_sum R D
    ((functorGraph R D E F).leftAt (F.obj d)) z d m
    (unitElement R (F.obj d)).val (add_zero i) (by omega : k + i = j) hij
  exact hN.trans (he.symm.trans (congrArg
    (fun x => (((BalancedTensor.rightHomMap R D M N
      ((functorGraph R D E F).leftAt (F.obj d))).f k z).v i j hij) x) hM.symm))

lemma dgExtensionUnitHomNaturality (M N : RightModule R D) :
    moduleHomPostcompose R D M N _ (functorExtensionUnit R D E F N) =
      ((dgModuleExtension R D E F).map M N ≫ moduleRestrictionHom R D E F.op _ _) ≫
        moduleHomPrecompose R D _ _ _ (functorExtensionUnit R D E F M) := by
  apply moduleHom_ext
  intro d
  calc
    _ = moduleHomπ R D M N d ≫ homPostcompose (M.obj (op d))
        (functorExtensionInsertionComponent R D E F N d) := by
      rw [moduleHomPostcompose_π]
      change _ ≫ homPostcompose _ ((moduleEvaluation R D d).map
        (functorExtensionUnit R D E F N)) = _
      rw [functorExtensionUnit_eval]
    _ = ((dgModuleExtension R D E F).map M N ≫ moduleHomπ R E _ _ (F.obj d)) ≫
        homPrecompose (functorExtensionInsertionComponent R D E F M d) _ :=
      dgExtensionUnitHomNaturality_eval R D E F M N d
    _ = _ := by
      rw [Category.assoc _ _ (moduleHomπ R D _ _ d), moduleHomPrecompose_π]
      change _ = _ ≫ (_ ≫ homPrecompose ((moduleEvaluation R D d).map
        (functorExtensionUnit R D E F M)) _)
      rw [functorExtensionUnit_eval]
      have he : moduleRestrictionHom R D E F.op
          ((dgModuleExtension R D E F).obj M) ((dgModuleExtension R D E F).obj N) ≫
          moduleHomπ R D _ _ d = moduleHomπ R E _ _ (F.obj d) :=
        moduleRestrictionHom_π R D E F.op _ _ d
      let H := homPrecompose (functorExtensionInsertionComponent R D E F M d)
        (((dgModuleExtension R D E F).obj N).obj (op (F.obj d)))
      have hh := congrArg (fun q => (dgModuleExtension R D E F).map M N ≫ q ≫ H) he
      simpa only [Category.assoc] using hh.symm

/-- D の元の単位射を全成分に持つ厳密 dg 自然変換。 -/
def dgExtensionUnitStrict : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
    (DGFunctor.id (RightModule R D))
    ((dgModuleExtension R D E F).comp (dgModuleRestriction R D E F.op)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R D
    (fun M => functorExtensionUnit R D E F M) (fun M N => by
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
      exact dgExtensionUnitHomNaturality R D E F M N)

end SerrePositivity.KST.LocalizingInvariants
