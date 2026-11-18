module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanPinchedChainNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentPinchedStandard

/-!
# 元の標準 Hom 同型と実 Γ/pinched 同型の同じ合成

概要：元の標準 Hom の Γ 像を実 pinched 同型で送ると元の直接標準/pinched 同型になる。
方針：元の二つの線形模型同型と同じ逆を相殺する。
規約：元の三つの比較射を保つ。
使われ方：標準閉恒等辺の元の Γ 零次数像への照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

lemma standardDoldKanPinchedComparison (x y : D) :
    SSet.uliftFunctor.{v, u}.map
      (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := R) x y).hom (forget (ModuleCat R))) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso (R := R) x y).hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) x y).hom := by
  have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := R) x y).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModuleDoldKanIso (R := R) x y).inv = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModuleIso (R := R) x y).inv := by
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModuleDoldKanIso, Iso.trans_inv, Iso.hom_inv_id_assoc]
  have h := congrArg (fun f => Functor.whiskerRight f (forget (ModuleCat R))) hc
  change Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := R) x y).hom _ ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceDoldKanIso (R := R) x y).inv = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceStandardIso (R := R) x y).inv at h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, h]

end SerrePositivity.ComplexLimits
