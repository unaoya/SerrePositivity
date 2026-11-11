module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathSplitMaps
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathSplitOrientation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeAWComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentComposition

/-!
# Path の合成面の立方体評価

概要：切断点を含む Path の合成面の評価は、後半と前半の立方体評価の dg 合成である。
方針：左右の有限座標の和へ移送し、豊穣関手の合成保存と AW 評価の公式を適用する。
規約：左右の番号付けの連結は後半、前半の順で、降順の場合に標準の向きと一致する。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の dg 方程式の合成項。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：coherent 単体の合成面の Hom 写像は左右の立方体の AW 合成に等しい。
方針：Path の左右分解と座標射影の同定を単体ごとに使い、豊穣合成保存を適用する。
規約：後の射が後半、前の射が前半の区間。
使われ方：Kerodon 2.5.9（Tag 00SC） の合成面を全最大旗の AW 評価公式へ移す。 -/
lemma coherentCube_split_face
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (S : Finset (Set.Ioo a b)) (j : S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitFaceMap hab S j ≫
      s.map (.mk a) (.mk b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeAWCompositionMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s j.val.property.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s j.val.property.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)) := by
  apply CategoryTheory.NatTrans.ext
  funext n
  rcases n with ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  let H := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitInclusionMap S j).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm).app _ F)
  let f := (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeIntervalFunctor j.val.property.1 S)).app _ H
  let g := (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeIntervalFunctor j.val.property.2 S)).app _ H
  let f₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap j.val.property.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumRightMap ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)).app _ F)
  let g₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap j.val.property.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b)).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumLeftMap ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)).app _ F)
  have hf : f = f₀ := congrArg (fun φ ↦ φ.app (Opposite.op ⦋n⦌) F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitIntervalMap_left S j)
  have hg : g = g₀ := congrArg (fun φ ↦ φ.app (Opposite.op ⦋n⦌) F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitIntervalMap_right S j)
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitFaceMap hab S j).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm).app _ F) =
        f.prod' g ⋙ compFunctor (.mk a) (.mk j.val.val) (.mk b) := by
    refine CategoryTheory.Functor.ext (fun t ↦ ?_)
    exact congrArg (fun G ↦ G.obj (H.obj t)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeInsertFunctor_comp hab j)
  change (s.map (.mk a) (.mk b)).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitFaceMap hab S j).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm).app _ F)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW ((s.map (.mk j.val.val) (.mk b)).app _ g₀)
        ((s.map (.mk a) (.mk j.val.val)).app _ f₀)
  rw [hp, hf, hg]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentHom_comp_apply s f₀ g₀

/-- 概要：合成面の立方体評価は後半と前半の立方体評価の dg 合成である。
方針：座標同値で評価を移送し、実際の Hom 写像の AW 因子分解と全旗の合成公式を使う。
規約：次数は −(p+q)。番号付けが降順なら標準の合成面の向きとなる。
使われ方：HA 1.3.1.16 の dg 単体の方程式の合成項の評価。 -/
lemma cubeEvaluation_pathSplitFace
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (S : Finset (Set.Ioo a b)) (j : S) {p q : ℕ}
    (e : Fin p ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
    (f : Fin q ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitEnumeration S j e f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitFaceMap hab S j ≫ s.map (.mk a) (.mk b)) =
      compose R
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s j.val.property.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s j.val.property.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)))
        (show -(q : ℤ) + -(p : ℤ) = -((p + q : ℕ) : ℤ) by push_cast; omega) := by
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_imageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitFaceMap hab S j ≫ s.map (.mk a) (.mk b))).symm.trans ?_
  rw [coherentCube_split_face]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_AW_comp e f _ _

private lemma descendingEnumeration_heq_card {A : Type u} [LinearOrder A]
    (S : Finset A) {n : ℕ} (h : S.card = n) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration S) (Fin.revPerm.trans (S.orderIsoOfFin h).toEquiv) := by
  subst n
  rfl

private lemma cubeEvaluation_heq_enumeration {T : Type u} {m n : ℕ} (h : m = n)
    (e : Fin m ≃ T) (f : Fin n ≃ T) (he : HEq e f) {x y : D}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e φ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation f φ) := by
  cases h
  cases he
  rfl

/-- 概要：降順の標準の合成面の評価は後半と前半の標準成分の dg 合成である。
方針：左右の降順番号付けの連結の一意性と濃度の等式で合成面の評価を移す。
規約：濃度による次数表示の違いを異種等号で保持する。
使われ方：HA 1.3.1.16 の比較写像の標準成分での合成項の同定。 -/
lemma cubeEvaluation_pathSplitFace_descending
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (S : Finset (Set.Ioo a b)) (j : S) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration (S.erase j.val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitFaceMap hab S j ≫ s.map (.mk a) (.mk b)))
      (compose R
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s j.val.property.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s j.val.property.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val))
        (show -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val).card : ℤ) +
          -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b).card : ℤ) =
          -(((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b).card + (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val).card : ℕ) : ℤ)
            by push_cast; omega)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b)
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_pathSplitCoordinates S j
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitEnumeration_eq_descending S j e f
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration_strictAnti _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration_strictAnti _) h
  have he : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration (S.erase j.val)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitEnumeration S j e f) :=
    (descendingEnumeration_heq_card (S.erase j.val) h).trans (heq_of_eq hn.symm)
  refine (cubeEvaluation_heq_enumeration h _ _ he _).trans ?_
  exact heq_of_eq (cubeEvaluation_pathSplitFace s hab S j e f)

/-- 概要：番号付き1面の評価は削除番号付けで合成面を評価した値に等しい。
方針：1面の因子分解を使い、座標の同値による評価の可換性を適用する。
規約：追加の符号はない。
使われ方：Kerodon 2.5.9（Tag 00SC） の立方体境界の1面を標準の合成面へ戻す。 -/
lemma cubeEvaluation_coherent_face_one
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (Equiv.ulift.symm : Fin m ≃ ULift.{u} (Fin m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitFaceMap hab S (e i) ≫ s.map (.mk a) (.mk b)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation Equiv.ulift.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S ≫ s.map (.mk a) (.mk b)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap_face_one_factor, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_imageMap (Equiv.ulift.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i)) Equiv.ulift.symm _

/-- 概要：降順の番号付き1面の評価は左右の標準成分の dg 合成と異種等号で一致する。
方針：削除番号付けが降順であることから標準の合成面の評価へ移す。
規約：次数の濃度表示を保ち、追加の向きの符号を導入しない。
使われ方：HA 1.3.1.16 の dg 方程式の各合成項を座標1面から得る。 -/
lemma cubeEvaluation_coherent_face_one_comp
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (he : StrictAnti e) (i : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (Equiv.ulift.symm : Fin m ≃ ULift.{u} (Fin m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S))
      (compose R
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s (e i).val.property.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S (e i).val.val b))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s (e i).val.property.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a (e i).val.val))
        (show -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a (e i).val.val).card : ℤ) +
          -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S (e i).val.val b).card : ℤ) =
          -(((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S (e i).val.val b).card +
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a (e i).val.val).card : ℕ) : ℤ) by push_cast; omega)) := by
  rw [cubeEvaluation_coherent_face_one]
  have hS : S.card = m + 1 := by simpa using (Fintype.card_congr e).symm
  have hE : (S.erase (e i).val).card = m := by simp [hS]
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i =
      Fin.revPerm.trans ((S.erase (e i).val).orderIsoOfFin hE).toEquiv := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.strictAnti_enumeration_unique
    · intro r t hrt
      change (e (i.succAbove t)).val < (e (i.succAbove r)).val
      exact he (i.succAboveOrderEmb.strictMono hrt)
    · exact ((S.erase (e i).val).orderIsoOfFin hE).strictMono.comp_strictAnti Fin.rev_strictAnti
  have hEnum : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration (S.erase (e i).val)) :=
    (heq_of_eq hn).trans (descendingEnumeration_heq_card (S.erase (e i).val) hE).symm
  refine (cubeEvaluation_heq_enumeration hE.symm _ _ hEnum _).trans ?_
  exact cubeEvaluation_pathSplitFace_descending s hab S (e i)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
