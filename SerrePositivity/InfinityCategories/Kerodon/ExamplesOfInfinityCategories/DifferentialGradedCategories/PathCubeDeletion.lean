module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeImage
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ErasedEnumeration

/-!
# Path の立方体の座標0面と内部点の削除

概要：座標0面から Path への写像を、一点削除した内部点集合の立方体で表す。
方針：削除番号付けで残る座標を移送し、両端点を加える前の集合の像を比較する。
規約：削除面は内部点を含まない面で、向きには元の相対順序を使う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の dg 方程式の削除項。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：内部点集合の包含は Path への立方体写像と可換である。
方針：部分集合の像を二度取る操作を一度の像に直す。
規約：有限内部点を増やしても各 Path の両端点は同じ。
使われ方：Kerodon 2.5.9（Tag 00SC） の有限座標集合への制限。 -/
lemma pathCubeMap_mono (hab : a < b) {S T : Finset (Set.Ioo a b)} (h : S ⊆ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (fun z : S ↦ (⟨z.val, h z.property⟩ : T)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  let U := F.obj t
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab
    ((Subtype.val : T → Set.Ioo a b) '' ((fun z : S ↦ (⟨z.val, h z.property⟩ : T)) '' U)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab ((Subtype.val : S → Set.Ioo a b) '' U)
  rw [Set.image_image]

/-- 概要：番号付きの座標0面は一点削除した内部点集合の立方体を通る。
方針：succAbove の残りの座標を削除番号付けへ移し、集合の像を比較する。
規約：残りの座標は ULift した Fin とし、同じ宇宙を保つ。
使われ方：HA 1.3.1.16 の削除面を小さい Path の立方体へ戻す式。 -/
lemma pathCubeMap_face_zero (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (Equiv.ulift.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab (S.erase (e i).val) := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  let U := F.obj t
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab
    ((Subtype.val : S → Set.Ioo a b) '' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceEmbedding e i '' U)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab ((Subtype.val : ↥(S.erase (e i).val) → Set.Ioo a b) ''
        ((Equiv.ulift.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i)) '' U))
  rw [Set.image_image, Set.image_image]
  rfl

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：Path の座標0面の評価は一点削除した集合の立方体評価である。
方針：座標0面の写像の因子分解と番号付けの移送に対する評価の可換性を使う。
規約：削除後の番号付けは erasedEnumeration で、追加の置換符号はない。
使われ方：HA 1.3.1.16 の dg 単体の方程式の削除項の評価。 -/
lemma cubeEvaluation_pathFace_zero (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (i : Fin (m + 1))
    (φ : nerve (Path a b) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (Equiv.ulift.symm : Fin m ≃ ULift.{u} (Fin m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S ≫ φ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab (S.erase (e i).val) ≫ φ) := by
  rw [← Category.assoc, pathCubeMap_face_zero, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_imageMap (Equiv.ulift.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i))
    Equiv.ulift.symm _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
