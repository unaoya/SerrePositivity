module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.DoubleMappingCylinder

/-!
# 二重写像円筒からの射の普遍性

概要：中央の円筒と左右の対象からの整合する三射を一つの射へまとめる。
方針：余積と pushout の普遍性を順に使う。
規約：Segal 1974 Lemma 1.7 と Proposition 1.6 の模型の比較。
使われ方：一端ずつ貼る二段階の pushout 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open scoped _root_.Simplicial

/--
概要：整合する三射から二重写像円筒からの射を作る。
方針：左右の射を余積へまとめ、両端点の二つの式で pushout へ降ろす。
規約：中央は元の対象と標準区間の積からの射。
使われ方：二重写像円筒の別の普遍性への比較。
-/
def doubleMappingCylinderDesc {C A B T : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B)
    (h : C ⊗ Δ[1] ⟶ T) (a : A ⟶ T) (b : B ⟶ T)
    (h₀ : SSet.ι₀ ≫ h = f ≫ a) (h₁ : SSet.ι₁ ≫ h = g ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g ⟶ T :=
  pushout.desc h (coprod.desc a b) (by
    apply coprod.hom_ext
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inl_desc_assoc, coprod.inl_map_assoc,
        coprod.inl_desc] using h₀
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inr_desc_assoc, coprod.inr_map_assoc,
        coprod.inr_desc] using h₁)

/--
概要：二重写像円筒の desc の中央への制限。
方針：pushout の計算則を使う。
規約：中央は標準区間との積。
使われ方：普遍性の存在の確認。
-/
@[reassoc] theorem doubleMappingCylinder_middle_desc {C A B T : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (h : C ⊗ Δ[1] ⟶ T) (a : A ⟶ T) (b : B ⟶ T)
    (h₀ : SSet.ι₀ ≫ h = f ≫ a) (h₁ : SSet.ι₁ ≫ h = g ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc f g h a b h₀ h₁ = h :=
  pushout.inl_desc ..

/--
概要：二重写像円筒の desc の左の対象への制限。
方針：pushout と余積の計算則を使う。
規約：零端点側の対象。
使われ方：普遍性の存在の確認。
-/
@[reassoc] theorem doubleMappingCylinder_left_desc {C A B T : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (h : C ⊗ Δ[1] ⟶ T) (a : A ⟶ T) (b : B ⟶ T)
    (h₀ : SSet.ι₀ ≫ h = f ≫ a) (h₁ : SSet.ι₁ ≫ h = g ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc f g h a b h₀ h₁ = a := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left, Category.assoc]
  change coprod.inl ≫ (pushout.inr _ _ ≫ pushout.desc _ _ _) = a
  rw [pushout.inr_desc, coprod.inl_desc]

/--
概要：二重写像円筒の desc の右の対象への制限。
方針：pushout と余積の計算則を使う。
規約：一端点側の対象。
使われ方：普遍性の存在の確認。
-/
@[reassoc] theorem doubleMappingCylinder_right_desc {C A B T : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (h : C ⊗ Δ[1] ⟶ T) (a : A ⟶ T) (b : B ⟶ T)
    (h₀ : SSet.ι₀ ≫ h = f ≫ a) (h₁ : SSet.ι₁ ≫ h = g ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc f g h a b h₀ h₁ = b := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right, Category.assoc]
  change coprod.inr ≫ (pushout.inr _ _ ≫ pushout.desc _ _ _) = b
  rw [pushout.inr_desc, coprod.inr_desc]

/--
概要：二重写像円筒からの射は中央・左・右への制限で決まる。
方針：pushout と余積の一意性を使う。
規約：境界の整合の証明の選択は不要。
使われ方：二段階の pushout の普遍性の一意性。
-/
theorem _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderDesc.doubleMappingCylinder_hom_ext {C A B T : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B)
    {u v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g ⟶ T}
    (hm : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g ≫ u = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g ≫ v)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g ≫ u = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g ≫ v)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g ≫ u = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g ≫ v) : u = v := by
  apply pushout.hom_ext
  · exact hm
  · apply coprod.hom_ext
    · exact hl
    · exact hr

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderDesc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_hom_ext := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderDesc.doubleMappingCylinder_hom_ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_left_desc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_desc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_left_desc_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_desc_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_middle_desc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_desc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_middle_desc_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_desc_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_right_desc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_desc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinder_right_desc_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_desc_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderDesc._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.doubleMappingCylinderDesc.congr_simp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc.congr_simp
