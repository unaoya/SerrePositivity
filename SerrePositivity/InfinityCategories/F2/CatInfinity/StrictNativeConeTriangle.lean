module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.F2.CatInfinity.NativeConeTriangle
public import SerrePositivity.InfinityCategories.F1.WeightedCosliceTransport

/-!
概要：strict coherent 錐の三角形の三つの境界射の回収。
方針：指定した錐と円柱の面の厳密な等式を使う。
規約：三角形や辺を新しく選択しない。
使われ方：三つの比較三単体の指定同型の合成関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {I : Type u} [SmallCategory I] {C : Type v}
  [Category.{u} C] [SimplicialCategory C] {F : I ⥤ C}
/-- 概要：strict な錐の三角形の底辺は元の図式の射。
方針：錐の三角形の面と通常の脚の式を合わせる。
規約：対象と Hom の宇宙を独立に扱う。
使われ方：比較先の錐の指定三角形の同型の構成。 -/
lemma nativeConeTriangle_strict_zero (c : Cone F) {i j : I} (f : i ⟶ j) :
    (SimplicialNerve C).δ 0
        (nativeConeTriangle (HomotopyLimits.strictCoherentCone c)
          (ULift.up (nerve.edgeMk f).edge)) =
      (coherentNerveEdge (F.map f)).edge :=
  (nativeConeTriangle_zero _ _).trans (strictCoherentDiagram_edge _ f)
/-- 概要：strict な錐の三角形の長辺は通常の錐の終域への脚。
方針：錐の三角形の面と通常の脚の式を合わせる。
規約：対象と Hom の宇宙を独立に扱う。
使われ方：比較先の錐の指定三角形の同型の構成。 -/
lemma nativeConeTriangle_strict_one (c : Cone F) {i j : I} (f : i ⟶ j) :
    (SimplicialNerve C).δ 1
        (nativeConeTriangle (HomotopyLimits.strictCoherentCone c)
          (ULift.up (nerve.edgeMk f).edge)) =
      (coherentNerveEdge (c.π.app j)).edge := by
  let J := (SSet.uliftFunctor.{v, u}).obj (nerve I)
  have hk : J.δ 0 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ j) := by
    apply ULift.ext
    exact (nerve.edgeMk f).tgt_eq
  have h := nativeConeTriangle_face (HomotopyLimits.strictCoherentCone c)
    (ULift.up (nerve.edgeMk f).edge) (0 : Fin 2)
  exact h.trans ((congrArg (fun k : J _⦋0⦌ ↦
    (nativeConeLeg (HomotopyLimits.strictCoherentCone c) k).edge) hk).trans
      (nativeConeLeg_strict c j))
/-- 概要：strict な錐の三角形の最初の辺は通常の錐の始域への脚。
方針：錐の三角形の面と通常の脚の式を合わせる。
規約：対象と Hom の宇宙を独立に扱う。
使われ方：比較先の錐の指定三角形の同型の構成。 -/
lemma nativeConeTriangle_strict_two (c : Cone F) {i j : I} (f : i ⟶ j) :
    (SimplicialNerve C).δ 2
        (nativeConeTriangle (HomotopyLimits.strictCoherentCone c)
          (ULift.up (nerve.edgeMk f).edge)) =
      (coherentNerveEdge (c.π.app i)).edge := by
  let J := (SSet.uliftFunctor.{v, u}).obj (nerve I)
  have hk : J.δ 1 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ i) := by
    apply ULift.ext
    exact (nerve.edgeMk f).src_eq
  have h := nativeConeTriangle_face (HomotopyLimits.strictCoherentCone c)
    (ULift.up (nerve.edgeMk f).edge) (1 : Fin 2)
  exact h.trans ((congrArg (fun k : J _⦋0⦌ ↦
    (nativeConeLeg (HomotopyLimits.strictCoherentCone c) k).edge) hk).trans
      (nativeConeLeg_strict c i))

end SerrePositivity.InfinityCategories.F2
