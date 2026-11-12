module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullUpperHomSquare
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullLowerHomSquare

/-!
概要：元上下二胞体の全 Hom 比較正方形を同じ共有対角比較で同時に保持する。
方針：具体的な指定零角比較と指定商比較をそれぞれ元合成端の辺とする。
規約：元全 Hom・元実混合二胞体を保持。Verdier 全図式比較は別工程。
使われ方：元上下二胞体を固定した coherent 全境界への接続データ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元上下二胞体の合成端を結ぶ同じ具体的混合比較辺。
方針：上側は指定零角の元混合三角形、下側は元指定商比較を使う。
規約：両比較辺を選び直さない。使われ方：両 Hom 正方形の指定右辺。 -/
def dgOdotMilnorNuNullTriangleCompositeComparisonEdge (j : Fin 2) :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge
      ((dgOdotMilnorNuNullTriangleFactor R d j).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}))
      ((dgOdotMilnorNuAbsoluteTriangleFactor R d h j).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u})) :=
  Fin.cases (dgOdotMilnorNuZeroMixedBoundaryEdge R d h)
    (fun k : Fin 1 => Fin.cases (dgOdotMilnorNuProjectionNullIntervalEdge R d h)
      (fun e : Fin 0 => Fin.elim0 e) k) j

/-- 概要：同じ共有対角比較を持つ元上下二胞体の全 Hom 比較正方形。
方針：構成済みの元上・下の全四辺固定正方形を同じ番号で束ねる。
規約：全 Hom と指定混合境界を保持。使われ方：coherent 全境界への同時接続。 -/
def dgOdotMilnorNuNullTriangleHomSquares (j : Fin 2) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ DGOdotMilnorNuNullCoherenceSpace R d :=
  ![dgOdotMilnorNuNullUpperHomSquare R d h, dgOdotMilnorNuNullLowerHomSquare R d h] j

/-- 概要：両正方形は元実／絶対全 Hom・同じ対角・指定混合比較を四辺に持つ。
方針：元上・下の四辺回収を同じ番号に適用する。
規約：全パラメータの等号。使われ方：指定二胞体付き全境界の保持。 -/
lemma dgOdotMilnorNuNullTriangleHomSquares_edges (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorNuNullTriangleHomSquares R d h j =
        dgOdotMilnorNuNullTriangleInterval R d j ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorNuNullTriangleHomSquares R d h j =
        dgOdotMilnorNuAbsoluteTriangleInterval R d h j ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorNuNullTriangleHomSquares R d h j =
        SSet.yonedaEquiv.symm (dgOdotMilnorNuNullDiagonalComparisonEdge R d h).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorNuNullTriangleHomSquares R d h j =
        SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangleCompositeComparisonEdge R d h j).edge := by
  fin_cases j
  · exact dgOdotMilnorNuNullUpperHomSquare_edges R d h
  · have he := dgOdotMilnorNuNullLowerHomSquare_edges R d h
    exact ⟨he.1, he.2.1, he.2.2.1,
      he.2.2.2.trans (dgOdotMilnorNuProjectionNullIntervalEdge_parameter R d h).symm⟩

/-- 概要：両比較正方形から元実二胞体の全 Hom 因子分解を厳密回収する。
方針：同じ区間同型と元上・下の回収式を使う。
規約：元全高次 Hom の等号。使われ方：元実面の保持。 -/
lemma dgOdotMilnorNuNullTriangleHomSquares_actual_fullHom (j : Fin 2) :
    dgOdotMilnorNuNullPathIntervalIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫
        dgOdotMilnorNuNullTriangleHomSquares R d h j = dgOdotMilnorNuNullTriangleFactor R d j := by
  fin_cases j
  · exact dgOdotMilnorNuNullUpperHomSquare_actual_fullHom R d h
  · exact dgOdotMilnorNuNullLowerHomSquare_actual_fullHom R d h

/-- 概要：両比較正方形から元絶対二胞体の全 Hom 因子分解を厳密回収する。
方針：同じ区間同型と元絶対上・下の回収式を使う。
規約：元全高次 Hom の等号。使われ方：元絶対面の保持。 -/
lemma dgOdotMilnorNuNullTriangleHomSquares_absolute_fullHom (j : Fin 2) :
    dgOdotMilnorNuNullPathIntervalIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫
        dgOdotMilnorNuNullTriangleHomSquares R d h j =
      dgOdotMilnorNuAbsoluteTriangleFactor R d h j := by
  fin_cases j
  · exact dgOdotMilnorNuNullUpperHomSquare_absolute_fullHom R d h
  · exact dgOdotMilnorNuNullLowerHomSquare_absolute_fullHom R d h

/-- 概要：元上下二胞体の比較は同じ共有対角の全比較辺で厳密に貼れる。
方針：同じ指定対角辺を持つ二つの四辺式を合成する。
規約：対角の選択を二面で変えない。使われ方：元上下二胞体付き全図式への接続。 -/
lemma dgOdotMilnorNuNullTriangleHomSquares_sharedDiagonal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorNuNullTriangleHomSquares R d h 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorNuNullTriangleHomSquares R d h 1 :=
  (dgOdotMilnorNuNullTriangleHomSquares_edges R d h 0).2.2.1.trans
    (dgOdotMilnorNuNullTriangleHomSquares_edges R d h 1).2.2.1.symm

/-- 概要：同じ比較正方形の元実側は元二胞体の豊穣 Hom 作用そのものを回収する。
方針：元全因子分解の回収と同じ零 Hom 包含を合成する。
規約：core 内の全単体の等号。使われ方：元実二胞体の全データの保持。 -/
lemma dgOdotMilnorNuNullTriangleHomSquares_actual_hom (j : Fin 2) :
    dgOdotMilnorNuNullPathIntervalIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫
        dgOdotMilnorNuNullTriangleHomSquares R d h j ≫ dgOdotMilnorNuNullCoherenceHom R d h =
      dgOdotMilnorNuNullTriangleHom R d j := by
  calc
    _ = (dgOdotMilnorNuNullPathIntervalIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫
        dgOdotMilnorNuNullTriangleHomSquares R d h j) ≫
          dgOdotMilnorNuNullCoherenceHom R d h := by simp only [Category.assoc]
    _ = dgOdotMilnorNuNullTriangleFactor R d j ≫ dgOdotMilnorNuNullCoherenceHom R d h :=
      congrArg (fun f => f ≫ dgOdotMilnorNuNullCoherenceHom R d h)
        (dgOdotMilnorNuNullTriangleHomSquares_actual_fullHom R d h j)
    _ = _ := dgOdotMilnorNuNullTriangleFactor_hom R d h j

/-- 概要：同じ比較正方形の元絶対側も元二胞体の豊穣 Hom 作用そのものを回収する。
方針：元絶対全因子分解の回収と同じ零 Hom 包含を合成する。
規約：core 内の全単体の等号。使われ方：元絶対二胞体の全データの保持。 -/
lemma dgOdotMilnorNuNullTriangleHomSquares_absolute_hom (j : Fin 2) :
    dgOdotMilnorNuNullPathIntervalIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫
        dgOdotMilnorNuNullTriangleHomSquares R d h j ≫ dgOdotMilnorNuNullCoherenceHom R d h =
      dgOdotMilnorNuAbsoluteTriangleHom R d h j := by
  calc
    _ = (dgOdotMilnorNuNullPathIntervalIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫
        dgOdotMilnorNuNullTriangleHomSquares R d h j) ≫
          dgOdotMilnorNuNullCoherenceHom R d h := by simp only [Category.assoc]
    _ = dgOdotMilnorNuAbsoluteTriangleFactor R d h j ≫ dgOdotMilnorNuNullCoherenceHom R d h :=
      congrArg (fun f => f ≫ dgOdotMilnorNuNullCoherenceHom R d h)
        (dgOdotMilnorNuNullTriangleHomSquares_absolute_fullHom R d h j)
    _ = _ := dgOdotMilnorNuAbsoluteTriangleFactor_hom R d h j

end SerrePositivity.KST.SConstruction
