module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPathInterval
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans

/-!
概要：元両三角形の全 Hom の区間表示を同じ零成分の実四辺として保持する。
方針：元共有対角・元最大合成を端点とし、指定商比較をそのまま使う。
規約：元の Hom 区間を別の辺へ置換しない。使われ方：零 Hom の比較正方形。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma nullIntervalEdgeParameter {X : SSet.{u}} (m : (Δ[1] : SSet.{u}) ⟶ X) :
    SSet.yonedaEquiv.symm
      ((SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u}).map m).edge = m := by
  have h : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u}.edge = 𝟙 (Δ[1] : SSet.{u}) := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  change SSet.yonedaEquiv.symm (m.app (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u}.edge) = m
  exact (SSet.yonedaEquiv_symm_comp (X := (Δ[1] : SSet.{u})) (Y := X)
    (n := ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u}.edge m).symm.trans
      ((congrArg (fun k => k ≫ m) h).trans (Category.id_comp m))

variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元実上下二単体の共有対角の零成分内の元頂点。
方針：同じ上三角形の因子分解を元対角で評価する。
規約：元下三角形とも厳密に同じ。使われ方：二面の共同比較端点。 -/
def dgOdotMilnorNuNullDiagonalVertex : DGOdotMilnorNuNullCoherenceSpace R d _⦋0⦌ :=
  (dgOdotMilnorNuNullTriangleFactor R d 0).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u})

/-- 概要：元実両区間の始点は同じ元共有対角。
方針：同じ逆同型の始点式と元上下対角の一致を使う。
規約：元頂点の等号。使われ方：比較正方形の左端。 -/
lemma dgOdotMilnorNuNullTriangleInterval_source (j : Fin 2) :
    (dgOdotMilnorNuNullTriangleInterval R d j).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = dgOdotMilnorNuNullDiagonalVertex R d := by
  have he := congrArg (fun x => (dgOdotMilnorNuNullTriangleFactor R d j).app
    (Opposite.op ⦋0⦌) x) dgOdotMilnorNuNullPathIntervalIso_source.{u}
  fin_cases j
  · exact he
  · exact he.trans (dgOdotMilnorNuNullTriangleFactor_diagonal R d).symm

/-- 概要：元実両区間の終点は同じ元最大合成。
方針：元逆同型の最大 path 回収を使う。
規約：元頂点の等号。使われ方：指定商比較の端点。 -/
lemma dgOdotMilnorNuNullTriangleInterval_target (j : Fin 2) :
    (dgOdotMilnorNuNullTriangleInterval R d j).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (dgOdotMilnorNuNullTriangleFactor R d j).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) :=
  congrArg (fun x => (dgOdotMilnorNuNullTriangleFactor R d j).app
    (Opposite.op ⦋0⦌) x) dgOdotMilnorNuNullPathIntervalIso_target.{u}

/-- 概要：元実三角形の全 Hom の同じ区間辺。
方針：元区間の恒等辺を同じ区間写像で写す。
規約：元全単体を保持。使われ方：零 Hom 正方形の実側の辺。 -/
def dgOdotMilnorNuNullTriangleIntervalEdge (j : Fin 2) :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge (dgOdotMilnorNuNullDiagonalVertex R d)
      ((dgOdotMilnorNuNullTriangleFactor R d j).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u})) :=
  ((SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u + 1}).map
    (dgOdotMilnorNuNullTriangleInterval R d j)).ofEq
      (dgOdotMilnorNuNullTriangleInterval_source R d j)
      (dgOdotMilnorNuNullTriangleInterval_target R d j)

/-- 概要：実側の元辺の Yoneda 射は同じ全 Hom の区間表示。
方針：恒等区間辺の Yoneda 自然性を使う。
規約：全パラメータの等号。使われ方：元二胞体の回収。 -/
lemma dgOdotMilnorNuNullTriangleIntervalEdge_parameter (j : Fin 2) :
    SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangleIntervalEdge R d j).edge =
      dgOdotMilnorNuNullTriangleInterval R d j := nullIntervalEdgeParameter _

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元絶対両二単体の同じ共有対角頂点。
方針：元絶対上三角形の全因子分解を評価する。
規約：元絶対下三角形とも同じ。使われ方：共同比較辺の終点。 -/
def dgOdotMilnorNuAbsoluteDiagonalVertex : DGOdotMilnorNuNullCoherenceSpace R d _⦋0⦌ :=
  (dgOdotMilnorNuAbsoluteTriangleFactor R d h 0).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u})

/-- 概要：元絶対両区間の始点は同じ元共有対角。
方針：元逆同型の始点と同じ絶対対角の一致を使う。
規約：元頂点の等号。使われ方：共同比較辺の終点。 -/
lemma dgOdotMilnorNuAbsoluteTriangleInterval_source (j : Fin 2) :
    (dgOdotMilnorNuAbsoluteTriangleInterval R d h j).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = dgOdotMilnorNuAbsoluteDiagonalVertex R d h := by
  have he := congrArg (fun x => (dgOdotMilnorNuAbsoluteTriangleFactor R d h j).app
    (Opposite.op ⦋0⦌) x) dgOdotMilnorNuNullPathIntervalIso_source.{u}
  fin_cases j
  · exact he
  · exact he.trans (dgOdotMilnorNuAbsoluteTriangleFactor_diagonal R d h).symm

/-- 概要：元絶対両区間の終点は同じ元最大合成。
方針：同じ逆同型の終点式を適用する。
規約：元頂点の等号。使われ方：元商比較の終点の保持。 -/
lemma dgOdotMilnorNuAbsoluteTriangleInterval_target (j : Fin 2) :
    (dgOdotMilnorNuAbsoluteTriangleInterval R d h j).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (dgOdotMilnorNuAbsoluteTriangleFactor R d h j).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) :=
  congrArg (fun x => (dgOdotMilnorNuAbsoluteTriangleFactor R d h j).app
    (Opposite.op ⦋0⦌) x) dgOdotMilnorNuNullPathIntervalIso_target.{u}

/-- 概要：元絶対三角形の全 Hom の同じ区間辺。
方針：同じ恒等区間辺を元区間表示で写す。
規約：元全単体を保持。使われ方：零 Hom 正方形の絶対側の辺。 -/
def dgOdotMilnorNuAbsoluteTriangleIntervalEdge (j : Fin 2) :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge (dgOdotMilnorNuAbsoluteDiagonalVertex R d h)
      ((dgOdotMilnorNuAbsoluteTriangleFactor R d h j).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u})) :=
  ((SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u + 1}).map
    (dgOdotMilnorNuAbsoluteTriangleInterval R d h j)).ofEq
      (dgOdotMilnorNuAbsoluteTriangleInterval_source R d h j)
      (dgOdotMilnorNuAbsoluteTriangleInterval_target R d h j)

/-- 概要：絶対側の元辺は同じ全 Hom の区間表示を厳密に回収する。
方針：恒等辺の Yoneda 自然性を使う。
規約：全パラメータの等号。使われ方：元絶対二胞体の保持。 -/
lemma dgOdotMilnorNuAbsoluteTriangleIntervalEdge_parameter (j : Fin 2) :
    SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteTriangleIntervalEdge R d h j).edge =
      dgOdotMilnorNuAbsoluteTriangleInterval R d h j := nullIntervalEdgeParameter _

/-- 概要：指定商比較の同じ前合成を零 Hom 内の実辺として保持する。
方針：元の全区間を写し、証明済みの両合成端に照合する。
規約：元比較辺を変更しない。使われ方：零 Hom 正方形の右辺。 -/
def dgOdotMilnorNuProjectionNullIntervalEdge :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge
      ((dgOdotMilnorNuNullTriangleFactor R d 1).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}))
      ((dgOdotMilnorNuAbsoluteTriangleFactor R d h 1).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u})) :=
  ((SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u + 1}).map
    (dgOdotMilnorNuProjectionNullFactor R d h)).ofEq
      (dgOdotMilnorNuProjectionNullFactor_source R d h)
      (dgOdotMilnorNuProjectionNullFactor_target R d h)

/-- 概要：右辺は元の指定商比較の全前合成パラメータそのもの。
方針：恒等区間辺の Yoneda 自然性を使う。
規約：全単体の等号。使われ方：指定商境界の厳密保持。 -/
lemma dgOdotMilnorNuProjectionNullIntervalEdge_parameter :
    SSet.yonedaEquiv.symm (dgOdotMilnorNuProjectionNullIntervalEdge R d h).edge =
      dgOdotMilnorNuProjectionNullFactor R d h := nullIntervalEdgeParameter _

/-- 概要：両元二単体に共通に使う同じ共有対角の比較辺。
方針：同じ可縮零成分内で一つの実辺を選ぶ。
規約：上下面で選び直さない。使われ方：零 Hom 比較正方形の左辺。 -/
def dgOdotMilnorNuNullDiagonalComparisonEdge :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge (dgOdotMilnorNuNullDiagonalVertex R d)
      (dgOdotMilnorNuAbsoluteDiagonalVertex R d h) :=
  Edge.ofTruncated (((dgOdotMilnorNuNullCoherenceSpace_contractible R d h).isTerminalVertex
    (dgOdotMilnorNuAbsoluteDiagonalVertex R d h)).nonempty_edge
      (dgOdotMilnorNuNullDiagonalVertex R d)).some

end SerrePositivity.KST.SConstruction
