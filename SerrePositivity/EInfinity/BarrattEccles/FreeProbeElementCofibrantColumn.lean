module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementColumnProperties
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraRelativeInput
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

/-- 概要：自由試験対象を元の cofibrancy と束ねる。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
def freeProbeElementCofibrantSource : CofibrantAlgebra A := by
  let := modelCategory A
  exact ⟨(freeProbeFunctor A).obj X, freeProbeFunctor_cofibrant A X⟩

/-- 概要：同じ要素圏上の全自由列を持ち上げる。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
def freeProbeElementCofibrantColumn : freeProbeElementIndex A X B.obj ⥤ CofibrantAlgebra A := by
  let := modelCategory A
  exact {
    obj s := ⟨(freeProbeElementColumn A X B.obj).obj s,
      freeProbeElementColumn_cofibrant A X B.obj s⟩
    map f := ObjectProperty.homMk ((freeProbeElementColumn A X B.obj).map f)
    map_id s := by
      apply ObjectProperty.hom_ext
      exact (freeProbeElementColumn A X B.obj).map_id s
    map_comp f g := by
      apply ObjectProperty.hom_ext
      exact (freeProbeElementColumn A X B.obj).map_comp f g }

/-- 概要：元の augmentation を全列で持ち上げる。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
def freeProbeElementCofibrantAugmentation : freeProbeElementCofibrantColumn A X B ⟶
    (Functor.const _).obj (freeProbeElementCofibrantSource A X) where
  app s := ObjectProperty.homMk ((freeProbeElementColumnAugmentation A X B.obj).app s)
  naturality s t f := by
    apply ObjectProperty.hom_ext
    exact (freeProbeElementColumnAugmentation A X B.obj).naturality f

/-- 概要：元の評価を全列で持ち上げる。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
def freeProbeElementCofibrantEvaluation : freeProbeElementCofibrantColumn A X B ⟶
    (Functor.const _).obj B where
  app s := ObjectProperty.homMk ((freeProbeElementColumnEvaluation A X B.obj).app s)
  naturality s t f := by
    apply ObjectProperty.hom_ext
    exact (freeProbeElementColumnEvaluation A X B.obj).naturality f

/-- 概要：持ち上げた augmentation の全成分の弱同値性。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
lemma freeProbeElementCofibrantAugmentation_weak (s : freeProbeElementIndex A X B.obj) :
    cofibrantAlgebraWeakEquivalences A ((freeProbeElementCofibrantAugmentation A X B).app s) := by
  let := modelCategory A
  exact freeProbeElementColumnAugmentation_weak A X B.obj s

/-- 概要：持ち上げた列の全射の弱同値性。
方針：元の列の構成と証明を保持して持ち上げる。
規約：基礎環・対象・射を変更しない。使われ方：全族 roof 比較の入力。 -/
lemma freeProbeElementCofibrantColumn_map_weak {s t : freeProbeElementIndex A X B.obj}
    (f : s ⟶ t) :
    cofibrantAlgebraWeakEquivalences A ((freeProbeElementCofibrantColumn A X B).map f) := by
  let := modelCategory A
  exact freeProbeElementColumn_map_weak A X B.obj f

end SerrePositivity.EInfinity.BarrattEccles
