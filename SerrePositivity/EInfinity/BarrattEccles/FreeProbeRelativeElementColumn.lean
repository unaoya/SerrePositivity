module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementCofibrantColumn
/-! 概要：元の要素圏上の自由 E∞ 列を cofibrant 相対圏へ持ち上げる。
方針：既存の各対象の cofibrancy と全列射・augmentation の弱同値性を使う。
規約：同じ対象・射・自然変換を保持し、モデル構造は局所的に選ぶ。
使われ方：標準導来単位比較の全 pinched 族を作る入力。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：元の要素圏の Hom 宇宙を DK 入力に揃える。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
abbrev freeProbeRelativeElementIndex : Type (u + 1) :=
  ULiftHom.{u + 1} (freeProbeElementIndex A X B.obj)

/-- 概要：同じ自由試験対象を DK 入力に置く。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
def freeProbeRelativeElementSource : (cofibrantAlgebraRelativeCategory A).category :=
  ULiftHom.objUp.{u + 1, u + 1} (freeProbeElementCofibrantSource A X)

/-- 概要：同じ列の Hom を ULift して DK 入力へ送る。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
def freeProbeRelativeElementColumn : freeProbeRelativeElementIndex A X B ⥤
    (cofibrantAlgebraRelativeCategory A).category :=
  ULiftHom.down.{u, u + 1, u + 1} ⋙ freeProbeElementCofibrantColumn A X B ⋙
    ULiftHom.up.{u, u + 1, u + 1}

/-- 概要：同じ augmentation の Hom を ULift する。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
def freeProbeRelativeElementAugmentation : freeProbeRelativeElementColumn A X B ⟶
    (Functor.const _).obj (freeProbeRelativeElementSource A X) :=
  Functor.whiskerLeft ULiftHom.down.{u, u + 1, u + 1}
    (Functor.whiskerRight (freeProbeElementCofibrantAugmentation A X B)
      ULiftHom.up.{u, u + 1, u + 1})

/-- 概要：同じ評価の Hom を ULift する。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
def freeProbeRelativeElementEvaluation : freeProbeRelativeElementColumn A X B ⟶
    (Functor.const _).obj (ULiftHom.objUp.{u + 1, u + 1} B) :=
  Functor.whiskerLeft ULiftHom.down.{u, u + 1, u + 1}
    (Functor.whiskerRight (freeProbeElementCofibrantEvaluation A X B)
      ULiftHom.up.{u, u + 1, u + 1})

/-- 概要：DK 入力の augmentation の全弱同値性。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
lemma freeProbeRelativeElementAugmentation_weak (s : freeProbeRelativeElementIndex A X B) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((freeProbeRelativeElementAugmentation A X B).app s) :=
  freeProbeElementCofibrantAugmentation_weak A X B (ULiftHom.objDown.{u + 1, u + 1} s)

/-- 概要：DK 入力の列の全射の弱同値性。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
lemma freeProbeRelativeElementColumn_map_weak {s t : freeProbeRelativeElementIndex A X B}
    (f : s ⟶ t) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((freeProbeRelativeElementColumn A X B).map f) :=
  freeProbeElementCofibrantColumn_map_weak A X B (ULiftHom.down.map f)

end SerrePositivity.EInfinity.BarrattEccles
