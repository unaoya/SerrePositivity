module

public import SerrePositivity.KST.Spectra.AnodyneMappingLifts
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence

/-!
概要：共通の anodyne な頂点包含を保つ射は Kan 標的への前合成で全基点 π 同型。
方針：二つの頂点評価の全境界充填を使い、合成の π 同型性を打ち消す。
規約：重みの源・終域自体の Kan 性は要求しない。
使われ方：Goerss–Jardine VII §4。BK の終頂点射の各段の写像空間による検出。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 同じ anodyne 部分を保つ射の指数による制限は全基点 π 同型。 -/
lemma pre_piIsomorphism_of_commonAnodyne {P A B : SSet.{u}}
    (i : P ⟶ A) (j : P ⟶ B) (hi : anodyneExtensions i) (hj : anodyneExtensions j)
    (f : A ⟶ B) (h : i ≫ f = j) (Y : SSet.{u}) [KanComplex Y] :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((pre f).app Y) := by
  have hiπ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_pre_rlp_monomorphisms i hi Y)
  have hjπ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_pre_rlp_monomorphisms j hj Y)
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := (pre i).app Y) _ hiπ
  have hh : (pre f).app Y ≫ (pre i).app Y = (pre j).app Y := by
    rw [← NatTrans.comp_app, ← pre_map, h]
  rw [hh]
  exact hjπ

end
end SerrePositivity.KST.Spectra
