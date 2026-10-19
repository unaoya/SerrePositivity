module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaUniverseNerve
public import SerrePositivity.InfinityCategories.Derived.DGModuleStability

/-! # 安定な全加群 nerve への dg Yoneda の実埋め込み

概要：元の nerve の対象宇宙だけを上げ、全加群 nerve 自体を標的にする。
方針：標的の持ち上げは既存の対象宇宙以下なので、ULift.down の実同型で除去する。
規約：標的は証明済みの dgModuleNerve。使われ方：前三角 dg 圏の安定性の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全加群 nerve の既存の宇宙以下の ULift は実同型で除去できる。 -/
def dgModuleNerveULiftIso :
    (SSet.uliftFunctor.{v, max (u + 1) v}).obj (dgModuleNerve A D) ≅ dgModuleNerve A D where
  hom := { app _ := ↾fun s => s.down }
  inv := { app _ := ↾fun s => ULift.up s }

/-- 元の dg nerve の対象宇宙だけを上げた、全加群 nerve への実 Yoneda 写像。 -/
def dgYonedaModuleNerve :
    (SSet.uliftFunctor.{max (u + 1) v, max u v}).obj (dgNerve A D) ⟶ dgModuleNerve A D :=
  dgYonedaUniverseNerve A D ≫ (dgModuleNerveULiftIso A D).hom

/-- 全加群 nerve への実 Yoneda 写像は写像空間で充満忠実。 -/
lemma dgYonedaModuleNerve_isFullyFaithful : IsFullyFaithful (dgYonedaModuleNerve A D) :=
  (dgYonedaUniverseNerve_isFullyFaithful A D).comp
    (qCatEquivalenceOfIso (dgModuleNerveULiftIso A D)).isQCatEquivalence.isFullyFaithful

/-- 実 Yoneda 写像の各単体への作用は元の dg Yoneda による単体の像。 -/
lemma dgYonedaModuleNerve_app {n : ℕ} (s : Simplex A D n) :
    (dgYonedaModuleNerve A D).app (Opposite.op ⦋n⦌) (ULift.up s) =
      s.map (dgYoneda A D) := rfl

/-- 元の対象の頂点は対応する表現可能加群の頂点へ写る。 -/
lemma dgYonedaModuleNerve_vertex (x : D) :
    (dgYonedaModuleNerve A D).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex x)) =
      Simplex.vertex ((dgYoneda A D).obj x) := by
  apply Simplex.vertexEquiv.injective
  rfl

end SerrePositivity.InfinityCategories
