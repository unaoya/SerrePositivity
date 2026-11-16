module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonInversion
public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization

/-!
# 元の Grothendieck 比較関手の成分ごとの弱同値不変性

概要：Cat 値図式の成分ごとの nerve 弱同値は元の全圏の比較関手を弱同値にする。
方針：元の Thomason 比較の自然性と bar の成分ごとの不変性を使う。
規約：モデル圏構造・遷移の可逆性・fiber の Kan 性は要求しない。
使われ方：二方向の Grothendieck 構成の係数の不変性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SerrePositivity.InfinityCategories

lemma grothendieck_map_isWeakHomotopyEquivalence {D : Type u} [Category.{u} D]
    {F G : D ⥤ Cat.{u, u}} (α : F ⟶ G)
    (hα : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (α.app d).toFunctor)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (Grothendieck.map α)) := by
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.map_localized_isIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveComparison α)
      (fun d => anodyneQ_map_isIso_of_weak _ (hα d)))
  have h := hb.comp (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map_isWeakHomotopyEquivalence G)
  rw [← _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map_naturality α] at h
  exact (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map_isWeakHomotopyEquivalence F).cancel_left h

end SerrePositivity.EInfinity.Hammock
