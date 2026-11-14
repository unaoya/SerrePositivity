module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.DoubleMappingCylinderMap
public import SerrePositivity.KST.Comparison.CylinderBoundary
public import SerrePositivity.KST.Comparison.LocalizedPushoutCube
public import SerrePositivity.KST.Comparison.LocalizedCoproductMaps
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 二重写像円筒の模型の局所化不変性

概要：span の各成分の局所化可逆な比較は、実際の二重写像円筒でも局所化可逆である。
方針：中央の円筒と両端の余積の可逆性を、単射な脚を持つ pushout の比較へ渡す。
規約：Segal 1974 Lemma 1.7 の模型の移行。homotopy-cartesian 性の貼り合わせそのものとは区別する。
使われ方：貼り合わせの定理を Kan な模型へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.SimplicialModel
open scoped _root_.Simplicial

/--
概要：円筒の両端点の余積の射は中央の対象の射と可換である。
方針：余積の二成分で円筒の端点の自然性を使う。
規約：二重写像円筒の pushout の比較の中央の四角形。
使われ方：pushout の標準比較射の構成。
-/
@[reassoc] theorem cylinderEndpoints_naturality {C C' : SSet.{u}} (c : C ⟶ C') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C ≫ (c ▷ Δ[1]) = coprod.map c c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C' := by
  apply coprod.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inl_desc_assoc, coprod.inl_map_assoc,
      coprod.inl_desc, SSet.ι₀_comp]
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inr_desc_assoc, coprod.inr_map_assoc,
      coprod.inr_desc, SSet.ι₁_comp]

/--
概要：各成分が局所化可逆な span の射は二重写像円筒の局所化可逆な射を誘導する。
方針：標準 pushout の比較の定理を使い、定義した比較射との一致を普遍性で確認する。
規約：Segal Lemma 1.7 の模型の不変性の補助。
使われ方：元の図式と Kan な図式の二重写像円筒の比較。
-/
@[kerodon 032S]
theorem doubleMappingCylinderMap_localized_isIso {C A B C' A' B' : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (f' : C' ⟶ A') (g' : C' ⟶ B')
    (c : C ⟶ C') (a : A ⟶ A') (b : B ⟶ B')
    (hf : c ≫ f' = f ≫ a) (hg : c ≫ g' = g ≫ b)
    (hc : IsIso (AnodyneHomotopy.anodyneQ.map c))
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hb : IsIso (AnodyneHomotopy.anodyneQ.map b)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf hg)) := by
  have e₁ := cylinderEndpoints_naturality c
  have e₂ : coprod.map f g ≫ coprod.map a b = coprod.map c c ≫ coprod.map f' g' := by
    rw [coprod.map_map, coprod.map_map, hf, hg]
  let q := pushout.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C') (coprod.map f' g') (c ▷ Δ[1]) (coprod.map a b) (coprod.map c c) e₁ e₂
  have hq : IsIso (AnodyneHomotopy.anodyneQ.map q) :=
    pushoutMap_localized_isIso _ _ _ _ _ _ _ (coprodMap_localized_isIso c c hc hc)
      (AnodyneHomotopy.whiskerRight_anodyneQ_isIso c hc _) (coprodMap_localized_isIso a b ha hb) e₁ e₂
  have he : q = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf hg := by
    apply pushout.hom_ext
    · exact (pushout.inl_desc _ _ _).trans
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_map f g f' g' c a b hf hg).symm
    · have hq₂ : pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g) ≫ q =
          coprod.map a b ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C') (coprod.map f' g') :=
        pushout.inr_desc _ _ _
      apply coprod.hom_ext
      · rw [hq₂, coprod.inl_map_assoc]
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left, Category.assoc] using
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_map f g f' g' c a b hf hg).symm
      · rw [hq₂, coprod.inr_map_assoc]
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right, Category.assoc] using
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_map f g f' g' c a b hf hg).symm
  exact he ▸ hq

end SerrePositivity.KST.Comparison
