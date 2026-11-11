module
public import SerrePositivity.KST.SConstruction.CofiberComparisonPrisms

/-! # 比較 prism の縦辺の形状
概要：三つの比較 prism の縦辺を、枠または固定 span の辺を通る形にする。
方針：標準辺の二頂点で形状を計算する。
規約：正方形の普遍性は不要。使われ方：点ごとの恒等辺の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：正方形の一つの頂点を通る時刻の辺。
方針：時刻を恒等、正方形を定値にする。
規約：x,y は端点。使われ方：比較 prism の縦辺。 -/
def squareVertexLine (x y : Fin 2) : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ (Δ[1] ⊗ Δ[1]) :=
  lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y))

/-- 概要：内部横座標の prism の左側は対角の枠を通る。
方針：パラメーター (i,i) と内部の水平辺を二頂点で計算する。
規約：y は上下の端点。使われ方：対角での恒等性。 -/
lemma arCofiberHorizontalPrism_left {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    squareVertexLine 0 y ≫ arCofiberHorizontalPrism a =
      lift (SSet.const (ComposableArrows.mk₀
        (⟨arObj a.down.val.1 a.down.val.1 le_rfl, Or.inr rfl⟩ : FrameAr n)))
        (lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm y))) ≫
          (frameInclusion n ▷ (Δ[1] ⊗ Δ[1] : SSet.{u})) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  · refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    fin_cases y <;> fin_cases r <;> rfl
  · apply Prod.ext
    · apply ULift.ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext r
      fin_cases r <;> rfl
    · rfl

/-- 概要：内部横座標の prism の右側は元の区間の角に定値。
方針：max(t,1)=1 と固定されたパラメーターを計算する。
規約：y は上下の端点。使われ方：右側の恒等性。 -/
lemma arCofiberHorizontalPrism_right {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    squareVertexLine 1 y ≫ arCofiberHorizontalPrism a =
      SSet.const (ComposableArrows.mk₀ a,
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm y)) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  · refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    fin_cases y <;> fin_cases r <;> rfl
  · apply Prod.ext
    · apply ULift.ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext r
      fin_cases r <;> rfl
    · rfl

/-- 概要：第二端点の prism の左側は固定 span の左辺を通る。
方針：区間の第二端点だけを動かし内部の横座標を零に保つ。
規約：y は上下の端点。使われ方：固定零射の適用。 -/
lemma arCofiberTargetPrism_left {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    squareVertexLine 0 y ≫ arCofiberTargetPrism a =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ arFixedStartSquare a)
        (SSet.const (stdSimplex.obj₀Equiv.symm y)) ≫
          (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  · refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    fin_cases y <;> fin_cases r <;> rfl
  · apply Prod.ext <;> rfl

/-- 概要：第二端点の prism の右側は元の区間の角に定値。
方針：max(t,1)=1 と内部座標の定値性を計算する。
規約：y は上下の端点。使われ方：右側の恒等性。 -/
lemma arCofiberTargetPrism_right {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    squareVertexLine 1 y ≫ arCofiberTargetPrism a =
      SSet.const (ComposableArrows.mk₀ a,
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm y)) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  · refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    fin_cases y <;> fin_cases r <;> rfl
  · apply Prod.ext <;> rfl

/-- 概要：第一端点の prism の下側は固定 span の下辺の終点を通る。
方針：区間の第一端点を動かし内部座標を (1,0) に保つ。
規約：x は左右の端点。使われ方：固定入力射の適用。 -/
lemma arCofiberSourcePrism_lower {n : ℕ} (a : Ar.{u} n) (x : Fin 2) :
    squareVertexLine x 0 ≫ arCofiberSourcePrism a =
      lift ((lift (SSet.const (stdSimplex.obj₀Equiv.symm x)) (𝟙 (Δ[1] : SSet.{u}))) ≫
        arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property)
        (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
          (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  · refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    fin_cases x <;> fin_cases r <;> rfl
  · apply Prod.ext <;> rfl

/-- 概要：第一端点の prism の上側は区間 (i,k) の右上角に定値。
方針：max(t,1)=1 と内部の右上角の定値性を計算する。
規約：x は左右の端点。使われ方：上側の恒等性。 -/
lemma arCofiberSourcePrism_upper {n : ℕ} (a : Ar.{u} n) (x : Fin 2) :
    squareVertexLine x 1 ≫ arCofiberSourcePrism a =
      SSet.const (ComposableArrows.mk₀
        (arObj a.down.val.1 (intervalStep a.down.val.1 a.down.val.2 a.down.property x)
          (le_intervalStep _ _ _ _)),
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  · refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    fin_cases x <;> fin_cases r <;> rfl
  · apply Prod.ext <;> rfl

/-- 概要：対角の枠内の水平辺は時刻に依存しない。
方針：二つの端点が等しい区間の形状を計算する。
規約：y は上下の端点。使われ方：内部横座標の prism の恒等性。 -/
lemma frameCofiberSquareMap_diagonal_horizontal {n : ℕ} (i : Fin (n + 1)) (y : Fin 2) :
    lift (SSet.const (ComposableArrows.mk₀
      (⟨arObj i i le_rfl, Or.inr rfl⟩ : FrameAr.{u} n)))
      (lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm y))) ≫
        frameCofiberSquareMap n =
      SSet.const (ComposableArrows.mk₀
        (arCofiberZeroInputOrder n (arObj i i le_rfl, ULift.up y))) := by
  apply SSet.yonedaEquiv.injective
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  fin_cases y <;> fin_cases r <;> rfl

/-- 概要：第一端点を保つ区間の左辺は第二端点に依存しない。
方針：固定 span の零射の形状を二頂点で計算する。
規約：y は上下の端点。使われ方：第二端点の prism の恒等性。 -/
lemma arCofiberZeroInputMap_fixedStart {n : ℕ} (a : Ar.{u} n) (y : Fin 2) :
    lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ arFixedStartSquare a)
      (SSet.const (stdSimplex.obj₀Equiv.symm y)) ≫ arCofiberZeroInputMap n =
      SSet.const (ComposableArrows.mk₀ (arCofiberZeroInputOrder n (a, ULift.up y))) := by
  apply SSet.yonedaEquiv.injective
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  fin_cases y <;> fin_cases r <;> rfl

/-- 概要：第二端点を保つ区間の下辺の終点は第一端点に依存しない。
方針：固定 span の入力射の形状を二頂点で計算する。
規約：x は左右の端点。使われ方：第一端点の prism の恒等性。 -/
lemma arCofiberInputMap_fixedTarget {n : ℕ} (a : Ar.{u} n) (x : Fin 2) :
    lift ((lift (SSet.const (stdSimplex.obj₀Equiv.symm x)) (𝟙 (Δ[1] : SSet.{u}))) ≫
      arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property)
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ arCofiberInputMap n =
      SSet.const (ComposableArrows.mk₀
        (⟨arObj 0 (intervalStep a.down.val.1 a.down.val.2 a.down.property x) (Fin.zero_le _),
          Or.inl rfl⟩ : FrameAr n)) := by
  apply SSet.yonedaEquiv.injective
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  fin_cases x <;> fin_cases r <;> rfl

end SerrePositivity.KST.SConstruction
