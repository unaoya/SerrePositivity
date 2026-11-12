module

public import SerrePositivity.KST.Comparison.StrictPushoutCube
public import SerrePositivity.KST.Comparison.CylinderBoundaryPullback
public import SerrePositivity.KST.Comparison.CoproductPullbacks

/-!
# 二重写像円筒への厳密な引き戻しの貼り合わせ

概要：span の二面が厳密な引き戻しなら、二重写像円筒への各頂点の四角形も引き戻しになる。
方針：円筒の境界の引き戻し性、余積と引き戻しの交換、adhesive 性を組み合わせる。
規約：Segal 1974 Lemma 1.7 の厳密な四角形に関する版。ホモトピー版は別に証明する。
使われ方：実際の二重写像円筒でファイバーを貼り合わせる。
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
概要：span の厳密な引き戻しから、二重写像円筒の中央と端点の余積の引き戻しを得る。
方針：境界の自然性と左右の引き戻しの余積を van Kampen の立方体に入れる。
規約：余分な境界の引き戻しの仮定を要求しない。
使われ方：左右の頂点の四角形を取り出す前の pushout の比較。
-/
theorem doubleMappingCylinderMap_isPullback {C A B C' A' B' : SSet.{u}}
    {f : C ⟶ A} {g : C ⟶ B} {f' : C' ⟶ A'} {g' : C' ⟶ B'}
    {c : C ⟶ C'} {a : A ⟶ A'} {b : B ⟶ B'}
    (hf : IsPullback f c a f') (hg : IsPullback g c b g') :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g) (c ▷ Δ[1])
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf.w.symm hg.w.symm)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f' g') ∧
    IsPullback (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g)) (coprod.map a b)
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf.w.symm hg.w.symm)
        (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C') (coprod.map f' g')) :=
  doubleMappingCylinderMap_strictCube f g f' g' c a b hf.w.symm hg.w.symm
    (cylinderEndpoints_isPullback c) (coproductSquare_isPullback hf hg)

/--
概要：span の厳密な引き戻しは、左頂点から二重写像円筒への引き戻しを与える。
方針：余積の包含の引き戻しを、円筒の余積側の引き戻しと貼り合わせる。
規約：Segal Lemma 1.7 の厳密な版の左頂点。
使われ方：二重写像円筒の比較のファイバーの計算。
-/
theorem doubleMappingCylinder_left_isPullback {C A B C' A' B' : SSet.{u}}
    {f : C ⟶ A} {g : C ⟶ B} {f' : C' ⟶ A'} {g' : C' ⟶ B'}
    {c : C ⟶ C'} {a : A ⟶ A'} {b : B ⟶ B'}
    (hf : IsPullback f c a f') (hg : IsPullback g c b g') :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g) a
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf.w.symm hg.w.symm)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f' g') :=
  (coproductInclusions_isPullback a b).1.paste_horiz
    (doubleMappingCylinderMap_isPullback hf hg).2

/--
概要：span の厳密な引き戻しは、右頂点から二重写像円筒への引き戻しを与える。
方針：余積の第二の包含の引き戻しを、円筒の余積側の引き戻しと貼り合わせる。
規約：Segal Lemma 1.7 の厳密な版の右頂点。
使われ方：二重写像円筒の比較のファイバーの計算。
-/
theorem doubleMappingCylinder_right_isPullback {C A B C' A' B' : SSet.{u}}
    {f : C ⟶ A} {g : C ⟶ B} {f' : C' ⟶ A'} {g' : C' ⟶ B'}
    {c : C ⟶ C'} {a : A ⟶ A'} {b : B ⟶ B'}
    (hf : IsPullback f c a f') (hg : IsPullback g c b g') :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g) b
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf.w.symm hg.w.symm)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f' g') :=
  (coproductInclusions_isPullback a b).2.paste_horiz
    (doubleMappingCylinderMap_isPullback hf hg).2

/--
概要：円筒の零端点の自然性は任意の中央の射について厳密な引き戻しである。
方針：端点の余積への第一の包含と、両端点の引き戻しを貼り合わせる。
規約：単体的区間の零端点を使う。
使われ方：span の中央の頂点から二重写像円筒への引き戻し。
-/
theorem cylinderZero_isPullback {C C' : SSet.{u}} (c : C ⟶ C') :
    IsPullback SSet.ι₀ c (c ▷ Δ[1]) SSet.ι₀ := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inl_desc] using
    (coproductInclusions_isPullback c c).1.paste_horiz (cylinderEndpoints_isPullback c)

/--
概要：span の厳密な引き戻しは、中央の頂点から二重写像円筒への引き戻しを与える。
方針：円筒の零端点の引き戻しと、円筒の中央の引き戻しを貼り合わせる。
規約：中央の頂点の写像は零端点を経由し、左の脚との合成にも一致する。
使われ方：Segal Lemma 1.7 の厳密な版の三つ目の頂点。
-/
theorem doubleMappingCylinder_center_isPullback {C A B C' A' B' : SSet.{u}}
    {f : C ⟶ A} {g : C ⟶ B} {f' : C' ⟶ A'} {g' : C' ⟶ B'}
    {c : C ⟶ C'} {a : A ⟶ A'} {b : B ⟶ B'}
    (hf : IsPullback f c a f') (hg : IsPullback g c b g') :
    IsPullback (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g) c
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf.w.symm hg.w.symm)
      (f' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f' g') := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_zero] using
    (cylinderZero_isPullback c).paste_horiz (doubleMappingCylinderMap_isPullback hf hg).1

end SerrePositivity.KST.Comparison
