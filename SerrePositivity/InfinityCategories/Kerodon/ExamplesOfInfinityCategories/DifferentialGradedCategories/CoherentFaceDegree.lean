module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentComponentDegree

/-!
# 同じ次数での coherent 立方体の座標面

概要：0面の評価を削除成分、1面の評価を左右の合成として同じ次数の等号で記述する。
方針：降順番号付けを保ち、既存の異種等号を次数を指定した成分へ移す。
規約：両辺の次数は残る座標数 m の負。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の立方体境界を dg 方程式へまとめる。

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

/-- 概要：降順の番号付き0面の評価は同じ次数を指定した削除成分に等しい。
方針：一点削除後の番号付けも降順であることから標準成分の評価へ移す。
規約：次数の等式を引数として保持する。
使われ方：Kerodon 2.5.9（Tag 00SC） の dg 方程式の削除項。 -/
lemma cubeEvaluation_coherent_face_zero_at
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (he : StrictAnti e) (i : Fin (m + 1))
    (hk : -(m : ℤ) = -((S.erase (e i).val).card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (Equiv.ulift.symm : Fin m ≃ ULift.{u} (Fin m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab (S.erase (e i).val) (-(m : ℤ)) hk := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation Equiv.ulift.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S ≫ s.map (.mk a) (.mk b)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_pathFace_zero]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_coherent_eq_componentAt s hab (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erasedEnumeration e i) _ hk
  intro r t hrt
  change (e (i.succAbove t)).val < (e (i.succAbove r)).val
  exact he (i.succAboveOrderEmb.strictMono hrt)

/-- 概要：降順の番号付き1面の評価は同じ終次数を指定した合成成分に等しい。
方針：合成面の異種等号と終次数を指定した合成の異種等号を合成する。
規約：向きは降順で、追加の符号を付けない。
使われ方：HA 1.3.1.16 の dg 方程式の合成項。 -/
lemma cubeEvaluation_coherent_face_one_at
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (he : StrictAnti e) (i : Fin (m + 1))
    (hk : -(m : ℤ) = 1 - (S.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (Equiv.ulift.symm : Fin m ≃ ULift.{u} (Fin m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeCompositionAt s hab S (e i) (-(m : ℤ)) hk := by
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_coherent_face_one_comp s hab e he i).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeCompositionAt_heq s hab S (e i) _ hk).symm)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
