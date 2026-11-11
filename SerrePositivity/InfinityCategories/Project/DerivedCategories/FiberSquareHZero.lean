module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberHomologySequence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ChainMapEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberConnectingShift

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded CochainComplex

open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)

/-- 概要：抽出した左 cospan 対象 B の頂点。
方針：既存の semifree 証明で包む。
規約：四角形では右下。使われ方：下辺と右辺の共通頂点。 -/
def derivedSquareBVertex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation_left F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)

/-- 概要：抽出した右 cospan 対象 C の頂点。
方針：既存の semifree 証明で包む。
規約：四角形では左上。使われ方：左辺と上辺の共通頂点。 -/
def derivedSquareCVertex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation_right F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)

/-- 概要：元の下辺の鎖写像を、その同じ一単体の辺として読む。
方針：鎖写像を閉零元へ送る。
規約：始点は元の錐頂点。使われ方：D5d の H⁰ の第一成分。 -/
def derivedSquareBottomDgEdge : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex (derivedSquareBVertex F) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomMap F)

/-- 概要：元の左辺の鎖写像を、その同じ一単体の辺として読む。
方針：鎖写像を閉零元へ送る。
規約：始点は元の錐頂点。使われ方：D5d の H⁰ の第二成分。 -/
def derivedSquareLeftDgEdge : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex (derivedSquareCVertex F) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftMap F)

/-- 概要：元の右辺の鎖写像を、その同じ一単体の辺として読む。
方針：抽出した左 cospan 射を閉零元へ送る。
規約：B から D への辺。使われ方：D5d の H⁰ の差の第一成分。 -/
def derivedSquareRightDgEdge : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S))
    (derivedSquareBVertex F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap

/-- 概要：元の上辺の鎖写像を、その同じ一単体の辺として読む。
方針：抽出した右 cospan 射を閉零元へ送る。
規約：C から D への辺、紙上の図式では下辺。使われ方：H⁰ の差の負の成分。 -/
def derivedSquareUpperDgEdge : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S))
    (derivedSquareCVertex F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap

/-- 概要：抽出した左 cospan 射は元の四角形の右辺と同じ一単体を与える。
方針：一単体からの鎖写像の復元公式と cospan の右辺の同定を使う。
規約：所属や整合性の追加前提なし。使われ方：右辺の固定。 -/
lemma derivedSquareRightMap_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap).edge =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap (SSet.yonedaEquiv
    (SSet.horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_simplexChainMap, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]

/-- 概要：抽出した右 cospan 射は元の四角形の上辺と同じ一単体を与える。
方針：終域の同定を消去し、一単体の復元と cospan の上辺の式を使う。
規約：紙上図式の下辺に対応する。使われ方：差の負の成分の固定。 -/
lemma derivedSquareUpperMap_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap).edge =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap (SSet.yonedaEquiv
    (SSet.horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))) ≫ eqToHom _)).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_comp_eqToHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_simplexChainMap, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge]

private lemma image_edge_eq {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) x y)
    (q : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)
    (he : (e.map ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).edge =
      SSet.yonedaEquiv (q ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) : e.edge = SSet.yonedaEquiv q := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_inclusion_injective S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S) 1
  exact he.trans (SSet.yonedaEquiv_comp q _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)

/-- 概要：正規化した下辺は元の四角形の下辺の一単体そのものである。
方針：包含での同定を充満包含の単射性で反映する。
規約：端点の表記だけを正規化する。使われ方：H⁰ の射を元の辺へ同定する。 -/
lemma derivedSquareBottomDgEdge_edge :
    (derivedSquareBottomDgEdge F).edge = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomEdge ≫ F) := by
  apply image_edge_eq (derivedSquareBottomDgEdge F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomEdge ≫ F)
  dsimp only [derivedSquareBottomDgEdge]
  simpa only [Category.assoc] using
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_inclusion (x := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex) (y := derivedSquareBVertex F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomMap F)).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomMap_edge F)

/-- 概要：正規化した左辺は元の四角形の左辺の一単体そのものである。
方針：包含像の同定と単射性を用いる。
規約：辺の選択はない。使われ方：H⁰ の第二成分の固定。 -/
lemma derivedSquareLeftDgEdge_edge :
    (derivedSquareLeftDgEdge F).edge = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftEdge ≫ F) := by
  apply image_edge_eq (derivedSquareLeftDgEdge F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftEdge ≫ F)
  dsimp only [derivedSquareLeftDgEdge]
  simpa only [Category.assoc] using
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_inclusion (x := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex) (y := derivedSquareCVertex F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftMap F)).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftMap_edge F)

/-- 概要：正規化した右辺は元の四角形の右辺の一単体そのものである。
方針：抽出した射の復元と包含の単射性を用いる。
規約：B から D の元の辺。使われ方：差の正の成分の固定。 -/
lemma derivedSquareRightDgEdge_edge :
    (derivedSquareRightDgEdge F).edge = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) := by
  apply image_edge_eq (derivedSquareRightDgEdge F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F)
  dsimp only [derivedSquareRightDgEdge]
  simpa only [Category.assoc] using
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_inclusion (x := derivedSquareBVertex F) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex
      F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap).trans (derivedSquareRightMap_edge F)

/-- 概要：正規化した上辺は元の四角形の上辺の一単体そのものである。
方針：抽出した射の復元と包含の単射性を用いる。
規約：紙上図式の C から D への下辺。使われ方：差の負の成分の固定。 -/
lemma derivedSquareUpperDgEdge_edge :
    (derivedSquareUpperDgEdge F).edge = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F) := by
  apply image_edge_eq (derivedSquareUpperDgEdge F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F)
  dsimp only [derivedSquareUpperDgEdge]
  simpa only [Category.assoc] using
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_inclusion (x := derivedSquareCVertex F) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex
      F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap).trans (derivedSquareUpperMap_edge F)

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：D3 の Hⁱ の元の二辺の対。
方針：下辺と左辺の Hⁱ の射を直和へ組む。
規約：辺は元と同じ一単体。使われ方：長完全列の第一射の Hⁱ 表示。 -/
def derivedSquareInfinityHomologyPair (i : ℤ) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone
  F).vertex ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i (derivedSquareBVertex F) ⊞ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i
      (derivedSquareCVertex F) :=
  biprod.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap S i (derivedSquareBottomDgEdge F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap S i (derivedSquareLeftDgEdge F))

/-- 概要：D3 の Hⁱ の元の二辺の差。
方針：右辺の Hⁱ と上辺の Hⁱ の負を直和からの射にする。
規約：紙上の右辺 − 下辺。使われ方：長完全列の第二射の Hⁱ 表示。 -/
def derivedSquareInfinityHomologyDifference (i : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i (derivedSquareBVertex F) ⊞ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i
      (derivedSquareCVertex F) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F) :=
  biprod.desc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap S i (derivedSquareRightDgEdge F))
    (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap S i (derivedSquareUpperDgEdge F))

/-- 概要：長完全列の第一射の各次数は D3 の二辺の対と一致する。
方針：直和の二射影で鎖写像の Hⁱ の自然性へ帰着する。
規約：D3 の同じ比較同型を用いる。使われ方：Π2 での Hⁱ の第一射の固定。 -/
theorem derivedSquareInfinityHomologyPair_comparison (i : ℤ) :
    derivedSquareInfinityHomologyPair F i ≫ biprod.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (derivedSquareBVertex F)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (derivedSquareCVertex F)).hom =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyPair
          F i := by
  apply biprod.hom_ext
  · simp only [derivedSquareInfinityHomologyPair, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyPair, Category.assoc,
      biprod.map_fst, biprod.lift_fst_assoc]
    dsimp only [derivedSquareBottomDgEdge]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_homology i (x := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex)
      (y := derivedSquareBVertex F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomMap F)).trans
        (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).hom ≫ k)
          (biprod.lift_fst (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomMap F) i)
            (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftMap F) i)).symm)
  · simp only [derivedSquareInfinityHomologyPair, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyPair, Category.assoc,
      biprod.map_snd, biprod.lift_snd_assoc]
    dsimp only [derivedSquareLeftDgEdge]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_homology i (x := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex)
      (y := derivedSquareCVertex F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftMap F)).trans
        (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).hom ≫ k)
          (biprod.lift_snd (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomMap F) i)
            (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftMap F) i)).symm)

/-- 概要：長完全列の第二射の各次数は D3 の二辺の差と一致する。
方針：直和の二包含で Hⁱ の自然性と負号の分配を使う。
規約：紙上の右辺 − 下辺。使われ方：Π2 での差写像の固定。 -/
theorem derivedSquareInfinityHomologyDifference_comparison (i : ℤ) :
    derivedSquareInfinityHomologyDifference F i ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).hom =
      biprod.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (derivedSquareBVertex F)).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (derivedSquareCVertex F)).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyDifference F i := by
  apply biprod.hom_ext'
  · simp only [derivedSquareInfinityHomologyDifference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyDifference,
      biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_homology i (x := derivedSquareBVertex F) (y :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap
  · simp only [derivedSquareInfinityHomologyDifference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyDifference,
      biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc, Preadditive.neg_comp,
      Preadditive.comp_neg]
    exact congrArg Neg.neg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_homology i (x := derivedSquareCVertex F) (y :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap)

/-- 概要：D5d の H⁰ の元の二辺の対。
方針：下辺と左辺の H⁰ の射を直和へ組む。
規約：辺は元と同じ一単体。使われ方：長完全列の第一射の H⁰ 表示。 -/
def derivedSquareHZeroPair : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S (derivedSquareBVertex F) ⊞ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S
      (derivedSquareCVertex F) :=
  biprod.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroMap S (derivedSquareBottomDgEdge F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroMap S (derivedSquareLeftDgEdge F))

/-- 概要：D5d の H⁰ の元の二辺の差。
方針：右辺の H⁰ と上辺の H⁰ の負を直和からの射にする。
規約：紙上の右辺 − 下辺。使われ方：長完全列の第二射の H⁰ 表示。 -/
def derivedSquareHZeroDifference :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S (derivedSquareBVertex F) ⊞ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S
      (derivedSquareCVertex F) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F) :=
  biprod.desc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroMap S (derivedSquareRightDgEdge F))
    (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroMap S (derivedSquareUpperDgEdge F))

/-- 概要：長完全列の第一射の零次は D5d の二辺の対と一致する。
方針：直和の二射影で鎖写像の H⁰ の自然性へ帰着する。
規約：D5d の同じ比較同型を用いる。使われ方：Π2 での H⁰ の第一射の固定。 -/
theorem derivedSquareHZeroPair_comparison :
    derivedSquareHZeroPair F ≫ biprod.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S (derivedSquareBVertex F)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S (derivedSquareCVertex F)).hom =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyPair F 0 :=
  derivedSquareInfinityHomologyPair_comparison F 0

/-- 概要：長完全列の第二射の零次は D5d の二辺の差と一致する。
方針：直和の二包含で H⁰ の自然性と負号の分配を使う。
規約：紙上の右辺 − 下辺。使われ方：Π2 での差写像の固定。 -/
theorem derivedSquareHZeroDifference_comparison :
    derivedSquareHZeroDifference F ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).hom =
      biprod.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S (derivedSquareBVertex F)).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S (derivedSquareCVertex F)).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyDifference F 0 :=
  derivedSquareInfinityHomologyDifference_comparison F 0

end SerrePositivity.InfinityCategories.Project.DerivedCategories
