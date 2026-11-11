module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeTransport

/-! # 固定頂点の余錐の輸送の prism 表示

概要：余錐を輸送した join の族を、実際の余錐の形をパラメーターとする prism に直す。
方針：join と直積の比較を使い、端点と基底への制限を計算する。
規約：時刻一の余錐と全時刻の基底を厳密に保つ。使われ方：余錐の関手圏の辺の持ち上げ。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

private lemma endpoint_as_point_whisker (A : SSet.{u}) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A = inv (snd (Δ[0] : SSet.{u}) A) ≫
      (SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm i) ▷ A) := by
  apply CartesianMonoidalCategory.hom_ext
  · change SSet.const (stdSimplex.obj₀Equiv.symm i) =
      inv (snd (Δ[0] : SSet.{u}) A) ≫ fst Δ[0] A ≫
        SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm i)
    rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]
  · change 𝟙 A = inv (snd (Δ[0] : SSet.{u}) A) ≫ snd Δ[0] A
    rw [IsIso.inv_hom_id]

/-- 概要：左直積比較は prism の端点を join の端点へ移す。
方針：標準零単体における比較の単位則と自然性を組み合わせる。
規約：join の二因子は任意。使われ方：余錐の輸送の終点の回収。 -/
lemma stable_joinTensorLeft_prismEndpoint (A B : SSet.{u}) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft (Δ[1] : SSet.{u}) A B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A) (𝟙 B) := by
  have hu : inv (snd (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft Δ[0] A B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (inv (snd (Δ[0] : SSet.{u}) A)) (𝟙 B) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (snd (Δ[0] : SSet.{u}) A) (𝟙 B))).1
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_unit, IsIso.inv_hom_id,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, IsIso.inv_hom_id, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id]
  rw [endpoint_as_point_whisker, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_naturality]
  rw [← Category.assoc, hu, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp,
    ← endpoint_as_point_whisker]

/-- 概要：図式の prism の終点の余錐を、余錐の形上の prism に持ち上げられる。
方針：頂点上の slice で輸送し、join と直積の比較を前合成する。
規約：終点の余錐・全時刻の基底・固定頂点を厳密に保つ。
使われ方：余錐の制限射の辺の持ち上げの具体的な入力。 -/
lemma exists_cocone_fixedVertex_prism {K X : SSet.{u}} [Quasicategory X]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⟶ X) (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ F) :
    ∃ L : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]) ≫ L = F ∧
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) ≫ L = H ∧
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]) ≫ L = snd Δ[1] Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ F := by
  obtain ⟨G, hG, hG₁, hGv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cocone_fixedVertex_transport F H hH
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft Δ[1] K Δ[0] ≫ G, ?_, ?_, ?_⟩
  · rw [← Category.assoc, stable_joinTensorLeft_prismEndpoint, hG₁]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_inl, hG]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_inr, Category.assoc, hGv]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
