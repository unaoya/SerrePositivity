module

public import SerrePositivity.KST.Descent.CoincidenceLocus
public import SerrePositivity.KST.Descent.ReducedClosedSubscheme

/-!
# 定理 3.1 の一致場所の被約閉中心

## 概要
section の一致場所の和を、基底上有限型の被約閉部分スキームとして実現する。

## 方針
既存の一致場所の閉性を消滅イデアル層の構成に入力し、台と次元の公式を適用する。

## 規約
非被約な等化子が被約中心へ必ずスキームとして因子分解するとは主張しない。
閉中心の台と、補開集合上の一致の排除を区別する。

## 使われ方
論文 定理 3.1 の軌道正方形の閉中心 Z と、その上の次元帰納。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {I : Type*} [Finite I]
variable {X Y : Over S} [IsSeparated Y.hom]

/-- 概要：有限個の射の一致場所の和を閉集合として束ねる（論文 定理 3.1）。
方針：等化子の像の有限和の閉性を使う。
規約：被約構造を入れる前の、基礎空間の閉集合。
使われ方：一致場所の被約閉部分スキームの構成。 -/
noncomputable def coincidenceClosedSet (sections : I → (X ⟶ Y)) : Closeds X.left :=
  ⟨coincidenceLocus sections, coincidenceLocus_isClosed sections⟩

variable (X : FiniteTypeSchemes S) (Y : Over S) [IsSeparated Y.hom]

/-- 概要：一致場所の和に入れた被約閉中心（論文 定理 3.1 の Z）。
方針：消滅イデアル層の閉部分スキームを基底上有限型の対象として構成する。
規約：始域の有限型性を保持し、単なる閉部分集合で終えない。
使われ方：前層 L の中心上の値と次元帰納。 -/
noncomputable def coincidenceCenter (sections : I → (X.obj ⟶ Y)) : FiniteTypeSchemes S :=
  reducedClosedAsFiniteType X (coincidenceClosedSet sections)

/-- 概要：有限型スキームの圏での一致場所の中心の包含（論文 定理 3.1）。
方針：消滅イデアル層の包含を基底 S 上の射として使う。
規約：前層 L が評価する圏の射そのもの。
使われ方：軌道正方形の中心への指定引き戻し。 -/
noncomputable def coincidenceCenterInclusion (sections : I → (X.obj ⟶ Y)) :
    coincidenceCenter X Y sections ⟶ X :=
  reducedClosedAsFiniteTypeInclusion X (coincidenceClosedSet sections)

/-- 概要：一致場所の中心は被約スキーム（論文 定理 3.1）。
方針：消滅イデアル層による閉部分スキームの被約性を使う。
規約：元の X の被約性はこの構成の被約性には不要。
使われ方：中心上での被約な基底への帰納。 -/
instance coincidenceCenter_isReduced (sections : I → (X.obj ⟶ Y)) :
    IsReduced (coincidenceCenter X Y sections).obj.left := by
  change IsReduced (reducedClosedSubscheme (coincidenceClosedSet sections))
  infer_instance

/-- 概要：一致場所の中心の包含は閉埋め込み（論文 定理 3.1）。
方針：被約閉部分スキームの包含の性質を使う。
規約：スキームの射としての閉埋め込み。
使われ方：抽象 blowup 正方形の閉中心の条件。 -/
instance coincidenceCenterInclusion_isClosedImmersion (sections : I → (X.obj ⟶ Y)) :
    IsClosedImmersion (coincidenceCenterInclusion X Y sections).hom.left := by
  change IsClosedImmersion (reducedClosedInclusion (coincidenceClosedSet sections))
  infer_instance

/-- 概要：一致場所の中心の像は元の一致場所の和（論文 定理 3.1）。
方針：被約閉中心の台の同定を使う。
規約：非被約な等化子のスキーム構造との同一視ではない。
使われ方：中心の補開集合と既存の一致の排除を接続する。 -/
theorem range_coincidenceCenterInclusion (sections : I → (X.obj ⟶ Y)) :
    Set.range (coincidenceCenterInclusion X Y sections).hom.left = coincidenceLocus sections :=
  range_reducedClosedInclusion (coincidenceClosedSet sections)

/-- 概要：相異なる射の被約閉中心は真閉（論文 定理 3.1）。
方針：包含の像を一致場所の和と同定し、その真閉性を使う。
規約：元の基底 X の既約性と被約性を仮定する。
使われ方：軌道正方形の真閉中心への帰納。 -/
theorem coincidenceCenterInclusion_range_ne_univ [IsReduced X.obj.left]
    [IrreducibleSpace X.obj.left] (sections : I → (X.obj ⟶ Y))
    (distinct : Function.Injective sections) :
    Set.range (coincidenceCenterInclusion X Y sections).hom.left ≠ Set.univ := by
  rw [range_coincidenceCenterInclusion]
  exact coincidenceLocus_ne_univ sections distinct

/-- 概要：一致場所の中心のスキームとしての次元は有限上界 d より小さい（定理 3.1）。
方針：中心と台の次元一致を使い、一致場所の真閉性から次元を下げる。
規約：型としての閉集合ではなく、実際の有限型被約スキームの次元を結論する。
使われ方：前層 L を中心上で評価した後の次元帰納。 -/
theorem coincidenceCenter_dimension_lt_bound [IsReduced X.obj.left]
    [IrreducibleSpace X.obj.left] (sections : I → (X.obj ⟶ Y))
    (distinct : Function.Injective sections) (d : ℕ)
    (bound : topologicalKrullDim X.obj.left ≤ d) :
    topologicalKrullDim (coincidenceCenter X Y sections).obj.left < d := by
  change topologicalKrullDim (reducedClosedSubscheme (coincidenceClosedSet sections)) < d
  rw [reducedClosedSubscheme_dimension]
  exact coincidenceLocus_dimension_lt_bound sections distinct d bound

end SerrePositivity.KST.Descent
