module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrowAugmentationLimits
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPrecomposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransWhiskering
/-! 概要：同じ通常列の全屋根は、反転関手の全自然同型に自然である。
方針：既存 QCat 双圏の交換則と関手の合成保存から通常列の全交換式を導く。
規約：元の全図式・augmentation・評価と同じ反転射を保持する。
使われ方：実 U の局所化源比較を元の複体屋根へ接続する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
open scoped _root_.Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  {E : SSet.{u}} [Quasicategory E]

/-- 概要：元の通常自然変換の全関手圏での像。
方針：同じ nerve の全射を後合成する。
規約：元の円柱を保持。使われ方：全屋根の二本の脚。 -/
def hom (F : nerve C ⟶ E) {V W : I ⥤ C} (a : V ⟶ W) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (nerveMap V ≫ F) (nerveMap W ≫ F) :=
  (hoFunctor.map ((ihom (nerve I)).map F)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom a)

omit [Quasicategory E] in
/-- 概要：元の全通常変換の像は同じ通常後合成で回収される。
方針：既存の nerve 自然変換の後合成式を使う。
規約：全図式を保持。使われ方：元の忘却像の全回収。 -/
lemma hom_whiskerRight {D : Type u} [Category.{u} D] (H : C ⥤ D)
    (F : nerve D ⟶ E) {V W : I ⥤ C} (a : V ⟶ W) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom (nerveMap H ≫ F) a = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F (Functor.whiskerRight a H) := by
  unfold _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerRight a H]
  have h₁ := Functor.map_comp (ihom (nerve I)) (nerveMap H) F
  have h₂ := Functor.map_comp hoFunctor ((ihom (nerve I)).map (nerveMap H))
    ((ihom (nerve I)).map F)
  have h : (hoFunctor.map ((ihom (nerve I)).map (nerveMap H ≫ F))).toFunctor =
      (hoFunctor.map ((ihom (nerve I)).map (nerveMap H))).toFunctor ⋙
        (hoFunctor.map ((ihom (nerve I)).map F)).toFunctor := by
    rw [h₁]
    exact congrArg Cat.Hom.toFunctor h₂
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    Functor.congr_hom h (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom a)

/-- 概要：元の弱 augmentation の全像は同じ全関手同型。
方針：元の全円柱の成分反転を使う。
規約：指定自然変換自身を保持。使われ方：元の屋根の左脚の反転。 -/
def augmentationIso (F : nerve C ⟶ E) (V : I ⥤ C) {X : C}
    (p : V ⟶ (Functor.const I).obj X)
    (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap V ≫ F) (nerveMap ((Functor.const I).obj X) ≫ F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy p) F)
  intro z
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective z
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy p) F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).edge =
      ((nerve.edgeMk (p.app i)).map F).edge := by
    exact congrArg (F.app (Opposite.op ⦋1⦌)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_component p i)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (hp i)

/-- 概要：指定した全同型の順射は元の augmentation の全像。
方針：同じ後合成円柱の式を使う。
規約：元の全射を保持。使われ方：全屋根のキャンセル。 -/
lemma augmentationIso_hom (F : nerve C ⟶ E) (V : I ⥤ C) {X : C}
    (p : V ⟶ (Functor.const I).obj X)
    (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p hp).hom = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F p := by
  change Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy p) F)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
  have hb : Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy p)) =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom p := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_hom p
  rw [hb]
  rfl

/-- 概要：全自然変換の像は元の後続自然同型に自然。
方針：全関手圏の交換則へ元の二射を代入する。
規約：全図式を保持。使われ方：元の屋根の二つの正方形。 -/
lemma hom_naturality {F G : nerve C ⟶ E} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G)
    {V W : I ⥤ C} (a : V ⟶ W) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F a ≫ (e.precomp (nerveMap W)).hom =
      (e.precomp (nerveMap V)).hom ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G a := by
  let α := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (nerveMap V) (nerveMap W)).symm (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom a)
  let β := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv F G).symm e.hom
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (nerveMap V ≫ F) (nerveMap W ≫ G))
    (Bicategory.whisker_exchange α β).symm
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (Bicategory.whiskerRight α (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (Bicategory.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap W)) β) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (Bicategory.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap V)) β) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (Bicategory.whiskerRight α (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight] at h
  have heV : (e.precomp (nerveMap V)).hom =
      (hoFunctor.map ((pre (nerveMap V)).app E)).toFunctor.map e.hom := rfl
  have heW : (e.precomp (nerveMap W)).hom =
      (hoFunctor.map ((pre (nerveMap W)).app E)).toFunctor.map e.hom := rfl
  rw [heV, heW]
  simpa only [α, β, Equiv.apply_symm_apply, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom] using h

/-- 概要：元の全屋根は同じ後続自然同型と可換。
方針：元の左右脚の全交換式から左脚を反転する。
規約：同じ全添字と元の左右脚を保持。使われ方：U の全源比較。 -/
lemma roof_naturality {F G : nerve C ⟶ E} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G)
    (V : I ⥤ C) {X Y : C} (p : V ⟶ (Functor.const I).obj X)
    (hpF : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)
    (hpG : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map G).toTruncated)
    (s : V ⟶ (Functor.const I).obj Y) :
    (e.precomp (nerveMap ((Functor.const I).obj X))).hom ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso G V p hpG).inv ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G s =
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p hpF).inv ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F s ≫
      (e.precomp (nerveMap ((Functor.const I).obj Y))).hom := by
  apply (cancel_epi (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p hpF).hom).mp
  have hp := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom_naturality e p
  rw [← _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso_hom F V p hpF, ← _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso_hom G V p hpG] at hp
  calc
    _ = ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p hpF).hom ≫
        (e.precomp (nerveMap ((Functor.const I).obj X))).hom) ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso G V p hpG).inv ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G s := by simp only [Category.assoc]
    _ = (e.precomp (nerveMap V)).hom ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G s := by
      rw [hp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F s ≫ (e.precomp (nerveMap ((Functor.const I).obj Y))).hom :=
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom_naturality e s).symm
    _ = _ := by simp only [Iso.hom_inv_id_assoc]

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn
