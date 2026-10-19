module
public import SerrePositivity.KST.SConstruction.FixedKanSpanBoundary

/-! # 定数境界を保つ二円柱の全パラメータでの相対合成
概要：元の二円柱を指定境界の逆・合成三角形を構成しながら一本の円柱へ合成する。
方針：退化境界三角形を、関手空間の制限 fibration に沿って全パラメータへ持ち上げる。
規約：境界三角形と恒等合成辺の入力は要求せず、元の定数性から構成する。
使われ方：元の二つの切断円柱を共通の Path パラメータで相対合成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {T U E : SSet.{u}} [KanComplex E] (j : T ⟶ U) [Mono j]
  {D F G : U ⟶ E} (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
  (ha : (j ▷ (Δ[1] : SSet.{u})) ≫ a.h = fst T Δ[1] ≫ j ≫ D)
  (hb : (j ▷ (Δ[1] : SSet.{u})) ≫ b.h = fst T Δ[1] ≫ j ≫ D)

/-- 元の定数境界から実三角形を構成して全族を相対合成する。 -/
def fixedKanHomotopySpanComposite : SSet.Homotopy F G :=
  relativeKanHomotopySpanComposite j a b (fixedKanHomotopySpanBoundary j a b ha hb).val

/-- 二つの元の円柱の相対合成は、元の指定境界を全時刻で厳密に固定する。 -/
lemma fixedKanHomotopySpanComposite_relative :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (fixedKanHomotopySpanComposite j a b ha hb).h =
      fst T Δ[1] ≫ j ≫ F :=
  relativeKanHomotopySpanComposite_restrict_constant j a b
    (fixedKanHomotopySpanBoundary j a b ha hb).val
    (fixedKanHomotopySpanBoundary j a b ha hb).property

/-- 相対合成は、二つの円柱の共通の元の始点の像そのものを境界で固定する。 -/
lemma fixedKanHomotopySpanComposite_relative_source :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (fixedKanHomotopySpanComposite j a b ha hb).h =
      fst T Δ[1] ≫ j ≫ D := by
  rw [fixedKanHomotopySpanComposite_relative, fixedHomotopySpanBoundary_target j a ha]

end SerrePositivity.KST.SConstruction
