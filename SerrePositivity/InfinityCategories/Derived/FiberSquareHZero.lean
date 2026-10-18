module
public import SerrePositivity.InfinityCategories.Derived.FiberHomologySequence
public import SerrePositivity.InfinityCategories.Derived.ChainMapEdge
public import SerrePositivity.InfinityCategories.Derived.FiberConnectingShift

/-! # 指定四辺と長完全列の H⁰ の整合

概要：長完全列の二辺の対・差は D5d の H⁰ の辺の射と一致する。
方針：四辺を同じ一単体で持つ辺に正規化し、鎖写像の H⁰ の自然性を適用する。
規約：四辺を置き換える追加仮定はない。使われ方：Π2 の元の商図式への輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve CochainComplex
open DGNerve.HomotopyComparison
open scoped Simplicial
variable {S : Type u} [CommRing S]
variable (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)

/-- 概要：抽出した左 cospan 対象 B の頂点。
方針：既存の semifree 証明で包む。
規約：四角形では右下。使われ方：下辺と右辺の共通頂点。 -/
def derivedSquareBVertex : (derivedInfinityCategory S) _⦋0⦌ :=
  Simplex.vertex (⟨(derivedSquarePresentation F).leftObj,
    derivedSquarePresentation_left F⟩ : Semifree S)

/-- 概要：抽出した右 cospan 対象 C の頂点。
方針：既存の semifree 証明で包む。
規約：四角形では左上。使われ方：左辺と上辺の共通頂点。 -/
def derivedSquareCVertex : (derivedInfinityCategory S) _⦋0⦌ :=
  Simplex.vertex (⟨(derivedSquarePresentation F).rightObj,
    derivedSquarePresentation_right F⟩ : Semifree S)

/-- 概要：元の下辺の鎖写像を、その同じ一単体の辺として読む。
方針：鎖写像を閉零元へ送る。
規約：始点は元の錐頂点。使われ方：D5d の H⁰ の第一成分。 -/
def derivedSquareBottomDgEdge : SSet.Truncated.Edge (X := twoTruncation S (Semifree S))
    (pullbackCone F).vertex (derivedSquareBVertex F) :=
  derivedChainMapEdge (derivedSquareBottomMap F)

/-- 概要：元の左辺の鎖写像を、その同じ一単体の辺として読む。
方針：鎖写像を閉零元へ送る。
規約：始点は元の錐頂点。使われ方：D5d の H⁰ の第二成分。 -/
def derivedSquareLeftDgEdge : SSet.Truncated.Edge (X := twoTruncation S (Semifree S))
    (pullbackCone F).vertex (derivedSquareCVertex F) :=
  derivedChainMapEdge (derivedSquareLeftMap F)

/-- 概要：元の右辺の鎖写像を、その同じ一単体の辺として読む。
方針：抽出した左 cospan 射を閉零元へ送る。
規約：B から D への辺。使われ方：D5d の H⁰ の差の第一成分。 -/
def derivedSquareRightDgEdge : SSet.Truncated.Edge (X := twoTruncation S (Semifree S))
    (derivedSquareBVertex F) (derivedSquareTargetVertex F) :=
  derivedChainMapEdge (derivedSquarePresentation F).leftMap

/-- 概要：元の上辺の鎖写像を、その同じ一単体の辺として読む。
方針：抽出した右 cospan 射を閉零元へ送る。
規約：C から D への辺、紙上の図式では下辺。使われ方：H⁰ の差の負の成分。 -/
def derivedSquareUpperDgEdge : SSet.Truncated.Edge (X := twoTruncation S (Semifree S))
    (derivedSquareCVertex F) (derivedSquareTargetVertex F) :=
  derivedChainMapEdge (derivedSquarePresentation F).rightMap

/-- 概要：抽出した左 cospan 射は元の四角形の右辺と同じ一単体を与える。
方針：一単体からの鎖写像の復元公式と cospan の右辺の同定を使う。
規約：所属や整合性の追加前提なし。使われ方：右辺の固定。 -/
lemma derivedSquareRightMap_edge :
    (complexEdge (derivedSquarePresentation F).leftMap).edge =
      SSet.yonedaEquiv (squareRightEdge ≫ (F ≫ derivedInfinityInclusion)) := by
  change (complexEdge (simplexChainMap (SSet.yonedaEquiv
    (SSet.horn₂₂.ι₀₂ ≫ pullbackCospan (F ≫ derivedInfinityInclusion))))).edge = _
  rw [complexEdge_simplexChainMap, pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge]

/-- 概要：抽出した右 cospan 射は元の四角形の上辺と同じ一単体を与える。
方針：終域の同定を消去し、一単体の復元と cospan の上辺の式を使う。
規約：紙上図式の下辺に対応する。使われ方：差の負の成分の固定。 -/
lemma derivedSquareUpperMap_edge :
    (complexEdge (derivedSquarePresentation F).rightMap).edge =
      SSet.yonedaEquiv (squareTopEdge ≫ (F ≫ derivedInfinityInclusion)) := by
  change (complexEdge (simplexChainMap (SSet.yonedaEquiv
    (SSet.horn₂₂.ι₁₂ ≫ pullbackCospan (F ≫ derivedInfinityInclusion))) ≫ eqToHom _)).edge = _
  rw [complexEdge_comp_eqToHom, complexEdge_simplexChainMap, pullbackCospan,
    ← Category.assoc, cospanSquareBoundary_topEdge]

private lemma image_edge_eq {x y : (derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := twoTruncation S (Semifree S)) x y)
    (q : (Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)
    (he : (e.map ((SSet.truncation 2).map derivedInfinityInclusion)).edge =
      SSet.yonedaEquiv (q ≫ derivedInfinityInclusion)) : e.edge = SSet.yonedaEquiv q := by
  apply map_inclusion_injective S (Complex S) (complexSemifree S) 1
  exact he.trans (SSet.yonedaEquiv_comp q derivedInfinityInclusion)

/-- 概要：正規化した下辺は元の四角形の下辺の一単体そのものである。
方針：包含での同定を充満包含の単射性で反映する。
規約：端点の表記だけを正規化する。使われ方：H⁰ の射を元の辺へ同定する。 -/
lemma derivedSquareBottomDgEdge_edge :
    (derivedSquareBottomDgEdge F).edge = SSet.yonedaEquiv (derivedSquareBottomEdge ≫ F) := by
  apply image_edge_eq (derivedSquareBottomDgEdge F) (derivedSquareBottomEdge ≫ F)
  dsimp only [derivedSquareBottomDgEdge]
  simpa only [Category.assoc] using
    (derivedChainMapEdge_inclusion (x := (pullbackCone F).vertex) (y := derivedSquareBVertex F)
      (derivedSquareBottomMap F)).trans (derivedSquareBottomMap_edge F)

/-- 概要：正規化した左辺は元の四角形の左辺の一単体そのものである。
方針：包含像の同定と単射性を用いる。
規約：辺の選択はない。使われ方：H⁰ の第二成分の固定。 -/
lemma derivedSquareLeftDgEdge_edge :
    (derivedSquareLeftDgEdge F).edge = SSet.yonedaEquiv (derivedSquareLeftEdge ≫ F) := by
  apply image_edge_eq (derivedSquareLeftDgEdge F) (derivedSquareLeftEdge ≫ F)
  dsimp only [derivedSquareLeftDgEdge]
  simpa only [Category.assoc] using
    (derivedChainMapEdge_inclusion (x := (pullbackCone F).vertex) (y := derivedSquareCVertex F)
      (derivedSquareLeftMap F)).trans (derivedSquareLeftMap_edge F)

/-- 概要：正規化した右辺は元の四角形の右辺の一単体そのものである。
方針：抽出した射の復元と包含の単射性を用いる。
規約：B から D の元の辺。使われ方：差の正の成分の固定。 -/
lemma derivedSquareRightDgEdge_edge :
    (derivedSquareRightDgEdge F).edge = SSet.yonedaEquiv (squareRightEdge ≫ F) := by
  apply image_edge_eq (derivedSquareRightDgEdge F) (squareRightEdge ≫ F)
  dsimp only [derivedSquareRightDgEdge]
  simpa only [Category.assoc] using
    (derivedChainMapEdge_inclusion (x := derivedSquareBVertex F) (y := derivedSquareTargetVertex
      F) (derivedSquarePresentation F).leftMap).trans (derivedSquareRightMap_edge F)

/-- 概要：正規化した上辺は元の四角形の上辺の一単体そのものである。
方針：抽出した射の復元と包含の単射性を用いる。
規約：紙上図式の C から D への下辺。使われ方：差の負の成分の固定。 -/
lemma derivedSquareUpperDgEdge_edge :
    (derivedSquareUpperDgEdge F).edge = SSet.yonedaEquiv (squareTopEdge ≫ F) := by
  apply image_edge_eq (derivedSquareUpperDgEdge F) (squareTopEdge ≫ F)
  dsimp only [derivedSquareUpperDgEdge]
  simpa only [Category.assoc] using
    (derivedChainMapEdge_inclusion (x := derivedSquareCVertex F) (y := derivedSquareTargetVertex
      F) (derivedSquarePresentation F).rightMap).trans (derivedSquareUpperMap_edge F)

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：D3 の Hⁱ の元の二辺の対。
方針：下辺と左辺の Hⁱ の射を直和へ組む。
規約：辺は元と同じ一単体。使われ方：長完全列の第一射の Hⁱ 表示。 -/
def derivedSquareInfinityHomologyPair (i : ℤ) : derivedInfinityHomology S i (pullbackCone
  F).vertex ⟶
    derivedInfinityHomology S i (derivedSquareBVertex F) ⊞ derivedInfinityHomology S i
      (derivedSquareCVertex F) :=
  biprod.lift (derivedInfinityHomologyMap S i (derivedSquareBottomDgEdge F))
    (derivedInfinityHomologyMap S i (derivedSquareLeftDgEdge F))

/-- 概要：D3 の Hⁱ の元の二辺の差。
方針：右辺の Hⁱ と上辺の Hⁱ の負を直和からの射にする。
規約：紙上の右辺 − 下辺。使われ方：長完全列の第二射の Hⁱ 表示。 -/
def derivedSquareInfinityHomologyDifference (i : ℤ) :
    derivedInfinityHomology S i (derivedSquareBVertex F) ⊞ derivedInfinityHomology S i
      (derivedSquareCVertex F) ⟶
      derivedInfinityHomology S i (derivedSquareTargetVertex F) :=
  biprod.desc (derivedInfinityHomologyMap S i (derivedSquareRightDgEdge F))
    (-derivedInfinityHomologyMap S i (derivedSquareUpperDgEdge F))

/-- 概要：長完全列の第一射の各次数は D3 の二辺の対と一致する。
方針：直和の二射影で鎖写像の Hⁱ の自然性へ帰着する。
規約：D3 の同じ比較同型を用いる。使われ方：Π2 での Hⁱ の第一射の固定。 -/
theorem derivedSquareInfinityHomologyPair_comparison (i : ℤ) :
    derivedSquareInfinityHomologyPair F i ≫ biprod.map
      (derivedInfinityHomologyIso S i (derivedSquareBVertex F)).hom
      (derivedInfinityHomologyIso S i (derivedSquareCVertex F)).hom =
        (derivedInfinityHomologyIso S i (pullbackCone F).vertex).hom ≫ derivedSquareHomologyPair
          F i := by
  apply biprod.hom_ext
  · simp only [derivedSquareInfinityHomologyPair, derivedSquareHomologyPair, Category.assoc,
      biprod.map_fst, biprod.lift_fst_assoc]
    dsimp only [derivedSquareBottomDgEdge]
    exact (derivedChainMapEdge_homology i (x := (pullbackCone F).vertex)
      (y := derivedSquareBVertex F) (derivedSquareBottomMap F)).trans
        (congrArg (fun k => (derivedInfinityHomologyIso S i (pullbackCone F).vertex).hom ≫ k)
          (biprod.lift_fst (HomologicalComplex.homologyMap (derivedSquareBottomMap F) i)
            (HomologicalComplex.homologyMap (derivedSquareLeftMap F) i)).symm)
  · simp only [derivedSquareInfinityHomologyPair, derivedSquareHomologyPair, Category.assoc,
      biprod.map_snd, biprod.lift_snd_assoc]
    dsimp only [derivedSquareLeftDgEdge]
    exact (derivedChainMapEdge_homology i (x := (pullbackCone F).vertex)
      (y := derivedSquareCVertex F) (derivedSquareLeftMap F)).trans
        (congrArg (fun k => (derivedInfinityHomologyIso S i (pullbackCone F).vertex).hom ≫ k)
          (biprod.lift_snd (HomologicalComplex.homologyMap (derivedSquareBottomMap F) i)
            (HomologicalComplex.homologyMap (derivedSquareLeftMap F) i)).symm)

/-- 概要：長完全列の第二射の各次数は D3 の二辺の差と一致する。
方針：直和の二包含で Hⁱ の自然性と負号の分配を使う。
規約：紙上の右辺 − 下辺。使われ方：Π2 での差写像の固定。 -/
theorem derivedSquareInfinityHomologyDifference_comparison (i : ℤ) :
    derivedSquareInfinityHomologyDifference F i ≫ (derivedInfinityHomologyIso S i
      (derivedSquareTargetVertex F)).hom =
      biprod.map (derivedInfinityHomologyIso S i (derivedSquareBVertex F)).hom
        (derivedInfinityHomologyIso S i (derivedSquareCVertex F)).hom ≫
          derivedSquareHomologyDifference F i := by
  apply biprod.hom_ext'
  · simp only [derivedSquareInfinityHomologyDifference, derivedSquareHomologyDifference,
      biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
    exact derivedChainMapEdge_homology i (x := derivedSquareBVertex F) (y :=
      derivedSquareTargetVertex F) (derivedSquarePresentation F).leftMap
  · simp only [derivedSquareInfinityHomologyDifference, derivedSquareHomologyDifference,
      biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc, Preadditive.neg_comp,
      Preadditive.comp_neg]
    exact congrArg Neg.neg (derivedChainMapEdge_homology i (x := derivedSquareCVertex F) (y :=
      derivedSquareTargetVertex F) (derivedSquarePresentation F).rightMap)

/-- 概要：D5d の H⁰ の元の二辺の対。
方針：下辺と左辺の H⁰ の射を直和へ組む。
規約：辺は元と同じ一単体。使われ方：長完全列の第一射の H⁰ 表示。 -/
def derivedSquareHZeroPair : derivedInfinityHZero S (pullbackCone F).vertex ⟶
    derivedInfinityHZero S (derivedSquareBVertex F) ⊞ derivedInfinityHZero S
      (derivedSquareCVertex F) :=
  biprod.lift (derivedInfinityHZeroMap S (derivedSquareBottomDgEdge F))
    (derivedInfinityHZeroMap S (derivedSquareLeftDgEdge F))

/-- 概要：D5d の H⁰ の元の二辺の差。
方針：右辺の H⁰ と上辺の H⁰ の負を直和からの射にする。
規約：紙上の右辺 − 下辺。使われ方：長完全列の第二射の H⁰ 表示。 -/
def derivedSquareHZeroDifference :
    derivedInfinityHZero S (derivedSquareBVertex F) ⊞ derivedInfinityHZero S
      (derivedSquareCVertex F) ⟶
      derivedInfinityHZero S (derivedSquareTargetVertex F) :=
  biprod.desc (derivedInfinityHZeroMap S (derivedSquareRightDgEdge F))
    (-derivedInfinityHZeroMap S (derivedSquareUpperDgEdge F))

/-- 概要：長完全列の第一射の零次は D5d の二辺の対と一致する。
方針：直和の二射影で鎖写像の H⁰ の自然性へ帰着する。
規約：D5d の同じ比較同型を用いる。使われ方：Π2 での H⁰ の第一射の固定。 -/
theorem derivedSquareHZeroPair_comparison :
    derivedSquareHZeroPair F ≫ biprod.map
      (derivedInfinityHZeroIso S (derivedSquareBVertex F)).hom
      (derivedInfinityHZeroIso S (derivedSquareCVertex F)).hom =
        (derivedInfinityHZeroIso S (pullbackCone F).vertex).hom ≫ derivedSquareHomologyPair F 0 :=
  derivedSquareInfinityHomologyPair_comparison F 0

/-- 概要：長完全列の第二射の零次は D5d の二辺の差と一致する。
方針：直和の二包含で H⁰ の自然性と負号の分配を使う。
規約：紙上の右辺 − 下辺。使われ方：Π2 での差写像の固定。 -/
theorem derivedSquareHZeroDifference_comparison :
    derivedSquareHZeroDifference F ≫ (derivedInfinityHZeroIso S (derivedSquareTargetVertex F)).hom =
      biprod.map (derivedInfinityHZeroIso S (derivedSquareBVertex F)).hom
        (derivedInfinityHZeroIso S (derivedSquareCVertex F)).hom ≫
          derivedSquareHomologyDifference F 0 :=
  derivedSquareInfinityHomologyDifference_comparison F 0

end SerrePositivity.InfinityCategories
