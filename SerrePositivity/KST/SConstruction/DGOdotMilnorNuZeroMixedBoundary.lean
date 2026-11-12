module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroMixedComposite
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullIntervalEdges

/-!
概要：指定零角の元混合三角形を元実／絶対上三角形の最大合成端へ照合する。
方針：元最大 path の全 Hom 回収と同じ実完全合成の頂点評価を使う。
規約：元混合二辺とその同じ実二単体を保持。使われ方：上零 Hom 正方形の指定右辺。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元零角混合合成の始点は元実上三角形の最大 path の同じ像。
方針：元零角経由合成の頂点評価と元二短辺の回収を照合する。
規約：元実二胞体の頂点の等号。使われ方：上比較正方形の実側端点。 -/
lemma dgOdotMilnorNuZeroMixedStart_eq :
    dgOdotMilnorNuZeroMixedStart R d =
      (dgOdotMilnorNuNullTriangleFactor R d 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) := by
  apply Subtype.ext
  have hs : (dgOdotMilnorNuZeroMixedStart R d).val =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B) (dgOdotMilnorNuNullTopComposite R d) := by
    rfl
  exact hs.trans (congrArg (fun x =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι.app (Opposite.op ⦋0⦌) x)
      (dgOdotMilnorNuNullUpperHom_maximal R d)).symm

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元零角混合合成の終点は同じ絶対上三角形の元最大 path の像。
方針：同じ標準零角経由の頂点評価と元絶対二短辺の回収を照合する。
規約：元絶対二胞体の頂点の等号。使われ方：上比較正方形の絶対側端点。 -/
lemma dgOdotMilnorNuZeroMixedTarget_eq :
    dgOdotMilnorNuZeroMixedTarget R d =
      (dgOdotMilnorNuAbsoluteTriangleFactor R d h 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) := by
  apply Subtype.ext
  exact (dgOdotMilnorNuStandardZeroNullHom_vertex R d (fromZeroCategory (B))).trans
    (congrArg (fun x =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι.app (Opposite.op ⦋0⦌) x)
        (dgOdotMilnorNuAbsoluteUpperHom_maximal R d h)).symm

/-- 概要：指定零角の元混合合成辺を元実／絶対上三角形の合成端に置く。
方針：元の両端の厳密等号だけで同じ実辺を輸送する。
規約：辺の全単体を変更しない。使われ方：上零 Hom 比較正方形の右辺。 -/
def dgOdotMilnorNuZeroMixedBoundaryEdge :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge
      ((dgOdotMilnorNuNullTriangleFactor R d 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}))
      ((dgOdotMilnorNuAbsoluteTriangleFactor R d h 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u})) :=
  (dgOdotMilnorNuZeroMixedCompositeEdge R d h).ofEq
    (dgOdotMilnorNuZeroMixedStart_eq R d) (dgOdotMilnorNuZeroMixedTarget_eq R d h)

/-- 概要：元混合第一辺を元実上三角形の合成端に置く。
方針：同じ始点の等号を使う。
規約：元比較辺を保持。使われ方：指定零角混合三角形の第一辺。 -/
def dgOdotMilnorNuZeroMixedBoundaryFirstEdge :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge
      ((dgOdotMilnorNuNullTriangleFactor R d 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}))
      (dgOdotMilnorNuZeroMixedMiddle R d) :=
  (dgOdotMilnorNuZeroMixedLeftEdge R d).ofEq (dgOdotMilnorNuZeroMixedStart_eq R d) rfl

/-- 概要：元混合第二辺を同じ絶対上三角形の合成端に置く。
方針：同じ終点の等号を使う。
規約：元比較辺を保持。使われ方：指定零角混合三角形の第二辺。 -/
def dgOdotMilnorNuZeroMixedBoundarySecondEdge :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge (dgOdotMilnorNuZeroMixedMiddle R d)
      ((dgOdotMilnorNuAbsoluteTriangleFactor R d h 0).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u})) :=
  (dgOdotMilnorNuZeroMixedTopEdge R d).ofEq rfl (dgOdotMilnorNuZeroMixedTarget_eq R d h)

/-- 概要：元上二胞体の端点へ輸送した同じ指定零角混合三角形。
方針：元実二単体と元三辺の全単体をそのまま保持する。
規約：新たな充填を選ばない。使われ方：零角成分を保つ全比較の合成面。 -/
def dgOdotMilnorNuZeroMixedBoundaryTriangle :
    SSet.Edge.CompStruct (dgOdotMilnorNuZeroMixedBoundaryFirstEdge R d)
      (dgOdotMilnorNuZeroMixedBoundarySecondEdge R d h)
      (dgOdotMilnorNuZeroMixedBoundaryEdge R d h) := by
  let transport {X : SSet.{u + 1}} {a b c a' c' : X _⦋0⦌}
      (f : X.Edge a b) (g : X.Edge b c) (k : X.Edge a c)
      (T : SSet.Edge.CompStruct f g k) (ha : a = a') (hc : c = c') :
      SSet.Edge.CompStruct (f.ofEq ha rfl) (g.ofEq rfl hc) (k.ofEq ha hc) :=
    SSet.Edge.CompStruct.mk T.simplex T.d₂ T.d₀ T.d₁
  exact transport (dgOdotMilnorNuZeroMixedLeftEdge R d)
    (dgOdotMilnorNuZeroMixedTopEdge R d) (dgOdotMilnorNuZeroMixedCompositeEdge R d h)
    (dgOdotMilnorNuZeroMixedCompositeTriangle R d h)
    (dgOdotMilnorNuZeroMixedStart_eq R d) (dgOdotMilnorNuZeroMixedTarget_eq R d h)

/-- 概要：端点照合後の混合三角形は同じ元実二単体を厳密に回収する。
方針：元の実単体を使う構成の定義。
規約：二胞体そのものの等号。使われ方：全図式比較での指定零角の保持。 -/
lemma dgOdotMilnorNuZeroMixedBoundaryTriangle_simplex :
    (dgOdotMilnorNuZeroMixedBoundaryTriangle R d h).simplex =
      (dgOdotMilnorNuZeroMixedCompositeTriangle R d h).simplex := rfl

end SerrePositivity.KST.SConstruction
