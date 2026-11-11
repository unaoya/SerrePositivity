module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeBranches
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingGluing

/-! # 対称 span 全体の余錐空間の自己引き戻し表示

概要：対称 span の余錐空間は、同じ辺の余錐空間の始点上の自己引き戻しと同型。
方針：両枝を同じ辺に揃え、余錐族の貼り合わせの存在と一意性を使う。
規約：値域の充填性や零対象性は不要。使われ方：ループ模型への比較の始域を全体の余錐空間に戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：対称 span の余錐空間への射は同じ辺に揃えた両枝で決まる。
方針：表示変更の同型を打ち消し、span の二枝での一意性に戻す。
規約：パラメータは任意。使われ方：自己引き戻し表示の一意性。 -/
lemma symmetricCoconeBranches_hom_ext {X T : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    {a b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y}
    (h₁ : a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFirst f y = b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFirst f y)
    (h₂ : a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSecond f y = b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSecond f y) : a = b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_hom_ext_of_pushout horn₂₀.isPushout (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y
  · apply (cancel_mono (eqToHom (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace q y)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left f f)))).1
    exact h₁
  · apply (cancel_mono (eqToHom (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace q y)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right f f)))).1
    exact h₂

/-- 概要：共通始点で一致する二つの指定辺の余錐族は対称 span 全体へ貼り合わさる。
方針：両枝の表示を元へ戻し、join で展開した貼り合わせを使う。
規約：同じ辺の余錐空間を両方の入力に使う。使われ方：自己引き戻し表示の存在部分。 -/
lemma exists_symmetricCoconeBranches_glue {X T : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (b c : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y)
    (h : b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y =
      c ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y) :
    ∃ a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y,
      a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFirst f y = b ∧ a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSecond f y = c := by
  let b' := b ≫ eqToHom (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace q y) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left f f).symm)
  let c' := c ≫ eqToHom (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace q y) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right f f).symm)
  have hh := congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) y)) h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap _ (stdSimplex.δ (1 : Fin 2)) y) ≫ _) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap _ (stdSimplex.δ (1 : Fin 2)) y) ≫ _) at hh
  have Hb := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_restrict_uncurry (SSet.yonedaEquiv.symm f.edge)
    (stdSimplex.δ (1 : Fin 2)) y b
  have Hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_restrict_uncurry (SSet.yonedaEquiv.symm f.edge)
    (stdSimplex.δ (1 : Fin 2)) y c
  have hhc := Hb.symm.trans (hh.trans Hc)
  have hh' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
      (b' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
      (c' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) y) := by
    have Hb' := congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_change_uncurry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left f f).symm y b)
    have Hc' := congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_change_uncurry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right f f).symm y c)
    exact Hb'.trans (hhc.trans Hc'.symm)
  obtain ⟨a, ha, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_coconeMappingSpace_glue horn₂₀.isPushout (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y b' c' hh'
  refine ⟨a, ?_, ?_⟩
  · change a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap _ horn₂₀.ι₀₁ y ≫ _) = b
    rw [← Category.assoc, ha]
    dsimp only [b']
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · change a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap _ horn₂₀.ι₀₂ y ≫ _) = c
    rw [← Category.assoc, hb]
    dsimp only [c']
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- 概要：対称 span の余錐空間は同じ枝の余錐空間の自己引き戻し。
方針：可換性と貼り合わせの存在・一意性を使う。
規約：全パラメータの普遍性。使われ方：ループ模型との比較の同型。 -/
lemma symmetricCoconeBranches_isPullback {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFirst f y) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSecond f y)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y) := by
  apply IsPullback.mk' (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeBranches_comm f y)
  · intro T a b h₁ h₂
    exact symmetricCoconeBranches_hom_ext f y h₁ h₂
  · intro T b c h
    exact exists_symmetricCoconeBranches_glue f y b c h

/-- 概要：対称 span 全体の余錐空間から同じ枝の自己引き戻しへの標準同型。
方針：証明した引き戻しの普遍性から標準引き戻しとの比較同型を取る。
規約：順方向の両成分は二枝の制限。使われ方：枝の自己引き戻しのループ比較へ接続する。 -/
def symmetricCoconeKernelPairIso {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y ≅
      pullback (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y) :=
  (symmetricCoconeBranches_isPullback f y).isoPullback

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
