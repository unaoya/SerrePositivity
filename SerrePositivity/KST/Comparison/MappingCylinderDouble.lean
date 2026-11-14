module

public import SerrePositivity.KST.Comparison.MappingCylinder
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.DoubleMappingCylinderDesc

/-!
# 二重写像円筒の二段階の pushout 表示

概要：片端を貼った mapping cylinder の残る端点を貼ると、既存の二重写像円筒になる。
方針：二重写像円筒の三部分からの desc の普遍性を使う。
規約：Segal 1974 Lemma 1.7、Proposition 1.6 の通常の pushout との比較。
使われ方：片方の脚が単射である場合の円筒の比較の局所化可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open scoped _root_.Simplicial

/--
概要：片端を貼った mapping cylinder から二重写像円筒への射。
方針：中央の円筒と左の対象への包含を元の pushout でまとめる。
規約：始域の零端点の付着を尊重する。
使われ方：二段階の pushout の第一の包含。
-/
def mappingCylinderToDouble {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    mappingCylinder f ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g :=
  pushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_zero f g)

/--
概要：片端の円筒からの射は中央の円筒への包含を保つ。
方針：pushout の第一成分を計算する。
規約：標準区間との積の部分。
使われ方：二段階の普遍性の計算。
-/
@[reassoc] theorem mappingCylinderTop_toDouble {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    mappingCylinderTop f ≫ mappingCylinderToDouble f g = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g :=
  pushout.inl_desc ..

/--
概要：片端の円筒からの射は左の対象の包含を保つ。
方針：pushout の第二成分を計算する。
規約：零端点に貼った対象。
使われ方：二段階の普遍性の計算。
-/
@[reassoc] theorem mappingCylinderBase_toDouble {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    mappingCylinderBase f ≫ mappingCylinderToDouble f g = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g :=
  pushout.inr_desc ..

/--
概要：残る端点は右の対象へ元の写像で貼り付けられる。
方針：中央の円筒への制限と二重写像円筒の一端点の式を使う。
規約：二段階の pushout の可換性。
使われ方：二つ目の付着の四角形。
-/
@[reassoc] theorem mappingCylinderEndpoint_toDouble {C A B : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) :
    mappingCylinderEndpoint f ≫ mappingCylinderToDouble f g =
      g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g := by
  rw [mappingCylinderEndpoint, Category.assoc, mappingCylinderTop_toDouble,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_one]

/--
概要：既存の二重写像円筒は、片端の mapping cylinder の残る端点を貼る pushout である。
方針：三部分の写像の desc と一意性から、二段階の普遍性を直接示す。
規約：span のどちらの脚にも単射性を要求しない。
使われ方：通常の pushout への比較を単射な脚を共有する pushout の比較に帰着する。
-/
theorem mappingCylinderToDouble_isPushout {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    IsPushout (mappingCylinderEndpoint f) g (mappingCylinderToDouble f g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g) := by
  refine IsPushout.mk' (mappingCylinderEndpoint_toDouble f g) ?_ ?_
  · intro T u v hC hB
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderDesc.doubleMappingCylinder_hom_ext f g
    · simpa only [← Category.assoc, mappingCylinderTop_toDouble] using
        congrArg (fun k => mappingCylinderTop f ≫ k) hC
    · simpa only [← Category.assoc, mappingCylinderBase_toDouble] using
        congrArg (fun k => mappingCylinderBase f ≫ k) hC
    · exact hB
  · intro T a b hab
    have h₀ : SSet.ι₀ ≫ (mappingCylinderTop f ≫ a) = f ≫ (mappingCylinderBase f ≫ a) := by
      rw [← Category.assoc]
      change (SSet.ι₀ ≫ pushout.inl _ _) ≫ a = f ≫ (pushout.inr _ _ ≫ a)
      rw [pushout.condition, Category.assoc]
    have h₁ : SSet.ι₁ ≫ (mappingCylinderTop f ≫ a) = g ≫ b := hab
    let l := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc f g (mappingCylinderTop f ≫ a)
      (mappingCylinderBase f ≫ a) b h₀ h₁
    refine ⟨l, ?_, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_desc ..⟩
    apply pushout.hom_ext
    · change mappingCylinderTop f ≫ (mappingCylinderToDouble f g ≫ l) = mappingCylinderTop f ≫ a
      rw [← Category.assoc, mappingCylinderTop_toDouble, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_desc]
    · change mappingCylinderBase f ≫ (mappingCylinderToDouble f g ≫ l) = mappingCylinderBase f ≫ a
      rw [← Category.assoc, mappingCylinderBase_toDouble, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_desc]

end SerrePositivity.KST.Comparison
