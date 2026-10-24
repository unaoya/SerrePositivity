module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.CompositionSquareTriangles
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.CompositionTriangleComparison
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCompositionTriangle
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaComparisonHomotopy
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.CompositionTriangleFamilyComparison
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomotopyComposition

/-!
概要：comma 正方形の実際の二単体から単位比較の経路を取り出す。
方針：上側を基準単位三角形と、下側を恒等合成の三角形と、それぞれ二辺を固定して比較する。
規約：元の正方形の coherence を合成の類の等式に置き換えない。
使われ方：B1 逆方向の、導来 fiber への coherence を保った比較の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単位から出る comma 正方形の四辺を定値関手の端点で認識する。
方針：標的族の展開・単位頂点の代表・終辺の代表の公式を使う。
規約：図式は元の関手正方形そのもの。
使われ方：正方形の上下の三角形を基準三角形と比較する。 -/
noncomputable def unitCommaCompositionSquare {A X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    FunctorCompositionSquare (unitCommaSectionVertexHomotopy (A := A) η x)
      (intervalFamilyHomotopy (unitCommaSquareTargetFamily η x w s ≫
        intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) (unitCommaFiberTargetVertex G x w)))
      (unitCommaVertexHomotopy G x w A) where
  diagram := s.functorSquare
  bottom := s.functorSquare_bottom
  top := by
    rw [s.functorSquare_top]
    apply congrArg curry
    change (β_ A (Δ[1] : SSet.{u})).hom ≫ s.target ≫ G =
      (β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry
        (unitCommaSquareTargetFamily η x w s ≫ intervalFunctorMap G _ _)
    rw [intervalFunctorMap_uncurry, unitCommaSquareTargetFamily_uncurry]
  left := s.functorSquare_left
  right := s.functorSquare_right

/-- 概要：基準の単位比較の辺から元の正方形の共通対角辺への実際のホモトピー。
方針：前辺・後辺を共有する基準三角形と正方形の上側を相対比較する。
規約：元の二単体を指定して比較し、両端は固定される。
使われ方：coherence を保った順方向の比較の第一部分。 -/
noncomputable def unitCommaCompositionUpperPath {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    SSet.Homotopy
      (curry (intervalFamilyHomotopy (unitCommaSquareTargetFamily η x w s ≫
        unitIntervalMap η x (unitCommaFiberTargetVertex G x w))).h)
      (curry (unitCommaCompositionSquare η x w s).diagonal.h) :=
  (unitIntervalCompositionTriangle_family η x (unitCommaFiberTargetVertex G x w)
    (unitCommaSquareTargetFamily η x w s)).diagonalHomotopy
      (unitCommaCompositionSquare η x w s).upperTriangle

/-- 概要：元の正方形の共通対角辺から指定した右辺への実際のホモトピー。
方針：元の下側の二単体と恒等合成の基準三角形を二辺固定で比較する。
規約：恒等辺と右辺を変えず、元の下側の二単体を入力に使う。
使われ方：coherence を保った順方向の比較の第二部分。 -/
noncomputable def unitCommaCompositionLowerPath {A X Y : SSet.{u}}
    [Quasicategory X] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    SSet.Homotopy (curry (unitCommaCompositionSquare η x w s).diagonal.h)
      (curry (unitCommaVertexHomotopy G x w A).h) :=
  (unitCommaCompositionSquare η x w s).lowerTriangle.diagonalHomotopy
    (identityFunctorCompositionTriangle (unitCommaVertexHomotopy G x w A))

/-- 概要：元の正方形の共通対角辺を X の写像空間の族とする。
方針：対角の関手の辺に族の逆表示を適用する。
規約：元の対角辺そのものを使う。
使われ方：単位比較の像と右辺を結ぶ経路の中間点。 -/
noncomputable def unitCommaCompositionDiagonalFamily {A X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    A ⟶ intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) (unitCommaFiberTargetVertex G x w)) :=
  intervalFamilyOfEdge (unitCommaCompositionSquare η x w s).diagonalEdge

/-- 概要：共通対角の族の表示は元の対角ホモトピーを回収する。
方針：辺と族の逆表示の厳密な公式。
規約：ホモトピーそのものの等式。
使われ方：元の上下の三角形を族の比較に渡す。 -/
lemma unitCommaCompositionDiagonalFamily_homotopy {A X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    intervalFamilyHomotopy (unitCommaCompositionDiagonalFamily η x w s) =
      (unitCommaCompositionSquare η x w s).diagonal :=
  intervalFamilyOfEdge_homotopy _

/-- 概要：基準単位比較の像から元の共通対角の族へ進む実際のホモトピー。
方針：元の上側の三角形と基準三角形を、二辺固定で比較して転置する。
規約：Hom の等式から任意のホモトピーを選び直さない。
使われ方：coherence を保つ順方向の比較の第一経路。 -/
noncomputable def unitCommaCompositionUpperFamilyPath {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    SSet.Homotopy (unitCommaSquareTargetFamily η x w s ≫
      unitIntervalMap η x (unitCommaFiberTargetVertex G x w))
      (unitCommaCompositionDiagonalFamily η x w s) := by
  let T₀ := unitIntervalCompositionTriangle_family η x (unitCommaFiberTargetVertex G x w)
    (unitCommaSquareTargetFamily η x w s)
  have T₁ : FunctorCompositionTriangle (unitCommaSectionVertexHomotopy (A := A) η x)
      (intervalFamilyHomotopy (unitCommaSquareTargetFamily η x w s ≫
        intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) (unitCommaFiberTargetVertex G x w)))
      (intervalFamilyHomotopy (unitCommaCompositionDiagonalFamily η x w s)) := by
    rw [unitCommaCompositionDiagonalFamily_homotopy]
    exact (unitCommaCompositionSquare η x w s).upperTriangle
  exact T₀.familyHomotopy T₁

/-- 概要：元の共通対角の族から正方形の右辺の族へ進む実際のホモトピー。
方針：元の下側と恒等合成の三角形を比較し、両端固定で転置する。
規約：正方形の元の二単体が経路の構成に入る。
使われ方：coherence を保つ順方向の比較の第二経路。 -/
noncomputable def unitCommaCompositionLowerFamilyPath {A X Y : SSet.{u}}
    [Quasicategory X] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    SSet.Homotopy (unitCommaCompositionDiagonalFamily η x w s) (unitCommaArrowFamily G x w A) := by
  have T₀ : FunctorCompositionTriangle (identityFunctorHomotopy (SSet.const x : A ⟶ X))
      (unitCommaVertexHomotopy G x w A)
      (intervalFamilyHomotopy (unitCommaCompositionDiagonalFamily η x w s)) := by
    rw [unitCommaCompositionDiagonalFamily_homotopy]
    exact (unitCommaCompositionSquare η x w s).lowerTriangle
  have T₁ : FunctorCompositionTriangle (identityFunctorHomotopy (SSet.const x : A ⟶ X))
      (unitCommaVertexHomotopy G x w A)
      (intervalFamilyHomotopy (unitCommaArrowFamily G x w A)) := by
    rw [unitCommaArrowFamily_homotopy]
    exact identityFunctorCompositionTriangle _
  exact T₀.familyHomotopy T₁

/-- 概要：元の comma 正方形の上下の二単体を用いた単位比較のホモトピー。
方針：二辺固定で比較した二つの経路を、指定二辺の合成三角形で合成する。
規約：単位比較の同値性は不要。元の正方形を構成の入力として保持する。
使われ方：comma 写像空間から導来 fiber へ進む比較の path 座標。 -/
noncomputable def unitCommaCoherentComparisonHomotopy {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    SSet.Homotopy (unitCommaSquareTargetFamily η x w s ≫
      unitIntervalMap η x (unitCommaFiberTargetVertex G x w)) (unitCommaArrowFamily G x w A) :=
  functorHomotopyComposite (unitCommaCompositionUpperFamilyPath η x w s)
    (unitCommaCompositionLowerFamilyPath η x w s)

/-- 概要：単位比較の経路は元の上側・下側由来の二経路を合成する二単体を持つ。
方針：指定二辺の合成三角形を公開する。
規約：経路の類の等式に弱めない。
使われ方：順方向の比較と正方形の coherence の照合。 -/
noncomputable def unitCommaCoherentComparisonTriangle {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    FunctorCompositionTriangle (unitCommaCompositionUpperFamilyPath η x w s)
      (unitCommaCompositionLowerFamilyPath η x w s) (unitCommaCoherentComparisonHomotopy η x w s) :=
  functorHomotopyCompositeTriangle _ _

end SerrePositivity.InfinityCategories
