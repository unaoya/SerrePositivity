module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathSplitCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathIntervalMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeSumFlags

/-!
# 左右に分けた Path の座標写像

概要：切断点を除いた座標を左右の和に移すと、各区間への Path の制限は和の射影になる。
方針：座標の逆写像が点の値を保つことを各単体の各頂点で使う。
規約：後半が和の左側、前半が和の右側。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の AW 立方体の合成公式と Path の合成面の接続。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：切断点を除いた有限座標を元の座標集合へ含める。
方針：erase の所属から元の集合への所属を取り、その像の立方体写像を使う。
規約：切断点はまだ挿入しない。
使われ方：Kerodon 2.5.9（Tag 00SC） の合成面の残る座標の包含。 -/
def pathSplitInclusionMap (S : Finset (Set.Ioo a b)) (j : S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube ↥(S.erase j.val) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube ↥S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (fun t : ↥(S.erase j.val) ↦ (⟨t.val, Finset.mem_of_mem_erase t.property⟩ : S))

/-- 概要：残る座標に切断点を挿入し、合成面の Path へ送る。
方針：元の有限集合への包含、切断点の挿入、両端点の付加を合成する。
規約：全ての Path が切断点を含む。
使われ方：HA 1.3.1.16 の座標1面を切断点の名前で表す写像。 -/
def pathSplitFaceMap (hab : a < b) (S : Finset (Set.Ioo a b)) (j : S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube ↥(S.erase j.val) ⟶ nerve (CategoryTheory.SimplicialThickening.Path a b) :=
  pathSplitInclusionMap S j ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeInsertFunctor j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S

private lemma split_image_right (S : Finset (Set.Ioo a b)) (j : S)
    (U : Set (↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) ⊕ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val))) :
    {z : Set.Ioo j.val.val b | ∃ t, t ∈ U ∧
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm t).val.val = z.val} =
      (Subtype.val : ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) → Set.Ioo j.val.val b) ''
        (Sum.inl ⁻¹' U) := by
  ext z
  constructor
  · rintro ⟨t, ht, he⟩
    cases t with
    | inl t =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv_symm_inl_val] at he
      exact ⟨t, ht, Subtype.ext he⟩
    | inr t =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv_symm_inr_val] at he
      have h : j.val.val < t.val.val := he.symm ▸ z.property.1
      exact False.elim ((lt_asymm t.val.property.2) h)
  · rintro ⟨t, ht, he⟩
    refine ⟨Sum.inl t, ht, ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv_symm_inl_val]
    exact congrArg Subtype.val he

private lemma split_image_left (S : Finset (Set.Ioo a b)) (j : S)
    (U : Set (↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) ⊕ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val))) :
    {z : Set.Ioo a j.val.val | ∃ t, t ∈ U ∧
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm t).val.val = z.val} =
      (Subtype.val : ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val) → Set.Ioo a j.val.val) ''
        (Sum.inr ⁻¹' U) := by
  ext z
  constructor
  · rintro ⟨t, ht, he⟩
    cases t with
    | inr t =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv_symm_inr_val] at he
      exact ⟨t, ht, Subtype.ext he⟩
    | inl t =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv_symm_inl_val] at he
      have h : t.val.val < j.val.val := he.symm ▸ z.property.2
      exact False.elim ((lt_asymm t.val.property.1) h)
  · rintro ⟨t, ht, he⟩
    refine ⟨Sum.inr t, ht, ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv_symm_inr_val]
    exact congrArg Subtype.val he

/-- 概要：左右の和の座標で後半の Path への制限は左の和への射影になる。
方針：後半の区間にある選択点は和の左側から来た点に限られる。
規約：切断点を挿入する前の座標集合から制限する。
使われ方：HA 1.3.1.16 の後の射の立方体の座標射影の同定。 -/
lemma pathSplitIntervalMap_right (S : Finset (Set.Ioo a b)) (j : S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm ≫ pathSplitInclusionMap S j ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeIntervalFunctor j.val.property.2 S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap j.val.property.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  let U := F.obj t
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior j.val.property.2
    {z | ∃ v : S, v ∈ (fun w : ↥(S.erase j.val) ↦
      (⟨w.val, Finset.mem_of_mem_erase w.property⟩ : S)) ''
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm '' U) ∧ v.val.val = z.val} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior j.val.property.2
        ((Subtype.val : ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) → Set.Ioo j.val.val b) '' (Sum.inl ⁻¹' U))
  congr 1
  rw [← split_image_right S j U, Set.image_image]
  ext z
  constructor
  · rintro ⟨v, ⟨w, hw, rfl⟩, he⟩
    exact ⟨w, hw, he⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨_, ⟨w, hw, rfl⟩, he⟩

/-- 概要：左右の和の座標で前半の Path への制限は右の和への射影になる。
方針：前半の区間にある選択点は和の右側から来た点に限られる。
規約：切断点を挿入する前の座標集合から制限する。
使われ方：HA 1.3.1.16 の前の射の立方体の座標射影の同定。 -/
lemma pathSplitIntervalMap_left (S : Finset (Set.Ioo a b)) (j : S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm ≫ pathSplitInclusionMap S j ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeIntervalFunctor j.val.property.1 S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap j.val.property.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val) := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  let U := F.obj t
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior j.val.property.1
    {z | ∃ v : S, v ∈ (fun w : ↥(S.erase j.val) ↦
      (⟨w.val, Finset.mem_of_mem_erase w.property⟩ : S)) ''
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm '' U) ∧ v.val.val = z.val} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior j.val.property.1
        ((Subtype.val : ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val) → Set.Ioo a j.val.val) '' (Sum.inr ⁻¹' U))
  congr 1
  rw [← split_image_left S j U, Set.image_image]
  ext z
  constructor
  · rintro ⟨v, ⟨w, hw, rfl⟩, he⟩
    exact ⟨w, hw, he⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨_, ⟨w, hw, rfl⟩, he⟩

/-- 概要：番号付きの座標1面は切断点の挿入による合成面の写像を通る。
方針：残る番号を削除番号付けへ移し、元の座標集合への包含の像を比較する。
規約：座標 i の点を切断点として扱う。
使われ方：HA 1.3.1.16 の立方体境界の番号付き1面を Path の合成面へ移す。 -/
lemma pathCubeMap_face_one_factor (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (Equiv.ulift.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i)) ≫ pathSplitFaceMap hab S (e i) := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  let U := F.obj t
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab ((Subtype.val : S → Set.Ioo a b) ''
    insert (e i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceEmbedding e i '' U)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab ((Subtype.val : S → Set.Ioo a b) ''
        insert (e i) ((fun w : ↥(S.erase (e i).val) ↦
          (⟨w.val, Finset.mem_of_mem_erase w.property⟩ : S)) ''
            ((Equiv.ulift.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i)) '' U)))
  rw [Set.image_image]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
