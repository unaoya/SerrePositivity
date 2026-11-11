module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTransportEnrichedFunctor
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.EnrichedOrdinaryFunctorWhisker

/-!
概要：指定された同型の始域・終域の豊穣評価は、分類後も全高次 Hom に自然。
方針：共役を始域同型で戻す式を、元の豊穣関手の前後合成の保存で移す。
規約：全ての局所 Hom を保持し、通常の射の自然性だけへ弱めない。
使われ方：同じ結合共役の分類像と Hom 輸送の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z w' z'
open CategoryTheory MonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 元の豊穣関手の後でも、指定された同型の共役は全 Hom に自然な同じ正方形を与える。 -/
lemma isoTransportEnriched_naturality
    (V : Type u) [Category.{v} V] [MonoidalCategory V]
    {C : Type w} [Category.{z} C] [EnrichedOrdinaryCategory V C]
    {D : Type w'} [Category.{z'} D] [EnrichedOrdinaryCategory V D]
    (F : EnrichedFunctor V C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTransportObject C) :
    F.map X.source Y.source ≫ eHomWhiskerLeft V (F.obj X.source)
        ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor V F).map Y.comparison.hom) =
      (Iso.eHomCongr V X.comparison Y.comparison).hom ≫ F.map X.target Y.target ≫
        eHomWhiskerRight V ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor V F).map X.comparison.hom) (F.obj Y.target) := by
  have hL := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor_whiskerLeft V F X.source Y.comparison.hom
  have hR := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor_whiskerRight V F X.comparison.hom Y.target
  have hN := congrArg (fun m ↦ m ≫ F.map X.source Y.target)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedHomCongr_naturality V X.comparison Y.comparison)
  exact hL.symm.trans (hN.symm.trans ((Category.assoc _ _ _).trans
    (congrArg (fun m ↦ (Iso.eHomCongr V X.comparison Y.comparison).hom ≫ m) hR)))

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
