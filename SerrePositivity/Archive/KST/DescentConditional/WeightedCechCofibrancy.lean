module

public import SerrePositivity.KST.Descent.WeightedCechFubini
public import SerrePositivity.HomotopicalAlgebra.Diagram.PostcompositionQuillen

/-!
# 積添字と反復した射影的模型の比較

## 概要
単体集合の積添字の射影的模型と、反復した射影的模型の curry/uncurry は Quillen 随伴をなす。

## 方針
右クラスを二つの添字で点ごとに検査し、随伴から左 Quillen 性を得る。

## 規約
射影的 cofibration を点ごとの cofibration と同一視しない。

## 使われ方
論文 補題 3.2・3.3 の二重 Čech の重みの cofibrancy と導来 Fubini への接続。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K L : Type u) [SmallCategory K] [SmallCategory L] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

local instance : IsLocallyPresentable.{u} (L ⥤ SSet.{u}) :=
  SerrePositivity.Smith.AccessibleLimits.functorCategory_isLocallyPresentable L

/-- 概要：curry は二つの実際の射影的模型の間で右 Quillen（論文 補題 3.2）。
方針：fibration と自明 fibration の成分を二つの添字で評価する。
規約：左クラスの点ごとの検査は使わない。
使われ方：反復重みを積添字の重みへ移す左 Quillen 性の導出。 -/
theorem cechCurry_isRightQuillen :
    let := Projective.modelCategory L I J
    let := Projective.modelCategory_generated L I J
    let := Projective.modelCategory K (Projective.generators L I) (Projective.generators L J)
    let := Projective.modelCategory (K × L) I J
    IsRightQuillen (Functor.curry (C := K) (D := L) (E := SSet.{u})) := by
  let := Projective.modelCategory L I J
  let := Projective.modelCategory_generated L I J
  let := Projective.modelCategory K (Projective.generators L I) (Projective.generators L J)
  let := Projective.modelCategory (K × L) I J
  constructor
  · intro X Y p hp k l
    exact hp (k, l)
  · intro X Y p hp
    exact ⟨fun k l ↦ hp.1 (k, l), fun k l ↦ hp.2 (k, l)⟩

/-- 概要：uncurry は二つの実際の射影的模型の間で左 Quillen（論文 補題 3.2）。
方針：同値からの実際の随伴と curry の右 Quillen 性を使う。
規約：モデル圏構造を仮定として追加せず、既存の生成から構成する。
使われ方：反復された cofibrant 重みの積添字への移送。 -/
theorem cechUncurry_isLeftQuillen :
    let := Projective.modelCategory L I J
    let := Projective.modelCategory_generated L I J
    let := Projective.modelCategory K (Projective.generators L I) (Projective.generators L J)
    let := Projective.modelCategory (K × L) I J
    IsLeftQuillen (Functor.uncurry (C := K) (D := L) (E := SSet.{u})) := by
  have h := cechCurry_isRightQuillen K L I J
  let := Projective.modelCategory L I J
  let := Projective.modelCategory_generated L I J
  let := Projective.modelCategory K (Projective.generators L I) (Projective.generators L J)
  let := Projective.modelCategory (K × L) I J
  exact (isLeftQuillen_iff_isRightQuillen
    (Functor.currying (C := K) (D := L) (E := SSet.{u})).toAdjunction).mpr h

variable [IsQuillenBifunctor (curriedTensor SSet.{u})]

/-- 概要：二つの射影的 cofibrant 重みの外テンソル積も cofibrant（論文 補題 3.2）。
方針：内側の重みとのテンソルの左 Quillen 性を外側の射影的模型へ上げ、uncurry で移す。
規約：点ごとの cofibrancy だけを仮定せず、実際の射影的 cofibrancy を使う。
使われ方：実際の二重 Čech の導来 Fubini の重み。 -/
theorem externalCechWeight_isCofibrant (W : K ⥤ SSet.{u}) (V : L ⥤ SSet.{u})
    (hW : let := Projective.modelCategory K I J; IsCofibrant W)
    (hV : let := Projective.modelCategory L I J; IsCofibrant V) :
    let := Projective.modelCategory (K × L) I J
    IsCofibrant (externalCechWeight K L W V) := by
  have hT := WeightedCones.tensorDiagram_isLeftQuillen L I J V hV
  have hU := cechUncurry_isLeftQuillen K L I J
  let := Projective.modelCategory L I J
  let := Projective.modelCategory_generated L I J
  have : IsLeftQuillen (WeightedCones.tensorDiagram L V) := hT
  have hWV := Projective.postcompose_isCofibrant K I J
    (Projective.generators L I) (Projective.generators L J)
    (WeightedCones.adjunction L V) W hW
  let := Projective.modelCategory K (Projective.generators L I) (Projective.generators L J)
  let := Projective.modelCategory (K × L) I J
  have : IsLeftQuillen (Functor.uncurry (C := K) (D := L) (E := SSet.{u})) := hU
  have : IsCofibrant (W ⋙ WeightedCones.tensorDiagram L V) := hWV
  have : (Functor.uncurry (C := K) (D := L) (E := SSet.{u})).IsLeftAdjoint :=
    (Functor.currying (C := K) (D := L) (E := SSet.{u})).toAdjunction.isLeftAdjoint
  have := Quillen.isCofibrant_obj
    (Functor.uncurry (C := K) (D := L) (E := SSet.{u})) (W ⋙ WeightedCones.tensorDiagram L V)
  exact isCofibrant_of_cofibration (externalCechWeightIso K L W V).inv

end SerrePositivity.KST.Descent
