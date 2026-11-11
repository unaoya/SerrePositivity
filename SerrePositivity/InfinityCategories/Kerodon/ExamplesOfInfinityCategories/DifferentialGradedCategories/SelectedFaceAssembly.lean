module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer

/-! # 部分境界と未知成分からの単体データ

概要：選んだ面からの既知成分と指定した未知成分を組み立て、既知の方程式を回収する。
方針：面に含まれる集合では回収した値、残りでは指定した値を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の六成分の値を入れる充填候補。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：既知成分を部分境界から、未知成分を指定された射族から取る単体データ。
方針：選んだ面に集合が含まれるかで分岐する。
規約：HA Proposition 1.3.1.10。使われ方：未知方程式を解いた後の充填候補。 -/
def assembleData {n : ℕ} (S : Finset (Fin (n + 3))) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj S hS σ)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2) where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj S hS σ
  hom I a b k hI ha hb hk :=
    if hknown : ∃ j ∈ S, j ∉ I then _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.recoverHom S hS σ I a b k hI ha hb hk hknown
    else unknown I a b k hI ha hb hk

/-- 概要：選んだ面の像に含まれる部分集合は既知。
方針：その面が飛ばす選んだ頂点を像が含まないことを使う。
規約：HA Proposition 1.3.1.10。使われ方：面への制限の分岐の簡約。 -/
lemma image_known {n : ℕ} (S : Finset (Fin (n + 3)))
    (j : Fin (n + 3)) (hjS : j ∈ S) (J : Finset (Fin (n + 2))) :
    ∃ l ∈ S, l ∉ J.image j.succAbove := by
  refine ⟨j, hjS, ?_⟩
  rintro hj
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hj
  exact Fin.succAbove_ne j x hx

/-- 概要：組み立てたデータの各面の像の成分は、元の選んだ面の成分と異種等号で一致する。
方針：像が既知であることから条件分岐を簡約し、回収の面との一致を使う。
規約：HA Proposition 1.3.1.10。使われ方：データ全体の面への制限の検証。 -/
lemma assembleData_hom_heq_face {n : ℕ} (S : Finset (Fin (n + 3))) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj S hS σ))
    (j : Fin (n + 3)) (hjS : j ∈ S) (J : Finset (Fin (n + 2)))
    (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    HEq (((assembleData S hS σ unknown).pullback j.succAboveOrderEmb.toOrderHom).hom
      J a b k hJ ha hb hk)
      ((σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).hom J a b k hJ ha hb hk) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    j.succAboveOrderEmb.injective.injOn]
  have hknown : ∃ l ∈ S, l ∉ J.image j.succAboveOrderEmb.toOrderHom := image_known S j hjS J
  simp only [assembleData, dite_eq_left hknown]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.recoverHom_heq_face S hS σ
  rfl

/-- 概要：組み立てたデータを選んだ任意の面に制限すると、元の選んだ面のデータに等しい。
方針：頂点の一致と各成分の異種等号での一致から、データの外延性を使う。
規約：HA Proposition 1.3.1.10。使われ方：既知の全ての方程式の面からの回収。 -/
lemma assembleData_pullback_face {n : ℕ} (S : Finset (Fin (n + 3))) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj S hS σ))
    (j : Fin (n + 3)) (hjS : j ∈ S) :
    (assembleData S hS σ unknown).pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).toSimplexData := by
  have hobj : ((assembleData S hS σ unknown).pullback j.succAboveOrderEmb.toOrderHom).obj =
      (σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).obj := by
    funext k
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.face_obj S hS σ j hjS k).symm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  exact assembleData_hom_heq_face S hS σ unknown j hjS

/-- 概要：選んだ全ての面に一致するデータは、その面に含まれる集合で方程式を満たす。
方針：集合を含む面を選び、単射による方程式の移送を使う。
規約：HA Proposition 1.3.1.10。使われ方：未知成分の置換後の既知方程式の検証。 -/
lemma equation_of_faces {n : ℕ} (S : Finset (Fin (n + 3)))
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2))
    (hfaces : ∀ j (hjS : j ∈ S), s.pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).toSimplexData)
    (I : Finset (Fin (n + 3))) (hknown : ∃ j ∈ S, j ∉ I) : s.Equation I := by
  let j := hknown.choose
  have hjS : j ∈ S := hknown.choose_spec.1
  have hj : j ∉ I := hknown.choose_spec.2
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hh := s.equation_image_of_pullback j.succAboveOrderEmb.toOrderHom
    (σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)) (hfaces j hjS) J j.succAboveOrderEmb.injective.injOn
  have hImage : J.image j.succAboveOrderEmb.toOrderHom = I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I j hj
  simpa only [hImage] using hh

/-- 概要：組み立てたデータは全ての既知集合で方程式を満たす。
方針：選んだ各面への制限が元の単体であることから方程式を移送する。
規約：HA Proposition 1.3.1.10。使われ方：検証すべき方程式を未知集合に限定する。 -/
lemma assembleData_equation {n : ℕ} (S : Finset (Fin (n + 3))) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj S hS σ))
    (I : Finset (Fin (n + 3))) (hknown : ∃ j ∈ S, j ∉ I) :
    (assembleData S hS σ unknown).Equation I :=
  equation_of_faces S σ _ (assembleData_pullback_face S hS σ unknown) I hknown

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly
