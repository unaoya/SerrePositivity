module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorUniverseShapes

/-!
概要：余錐積の宇宙比較は共有境界と旧族・下方族の全包含を保持する。
方針：直積の自然性と余錐の元の包含を、各因子の順で照合する。
規約：元の全写像の等号を証明する。
使われ方：小さい scalar comma の全拡張を同じ元の積へ戻す。
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の全包含を宇宙比較が保持。
方針：積と余錐の自然性。規約：全射の等号。使われ方：両全境界の回収。 -/
lemma coneTensorOldUniverseShape_boundary (A L : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (A ◁ joinInl L (Δ[0] : SSet.{u})) ≫
      coneTensorOldUniverseShape A L =
    (HomotopyLimits.uliftTensorIso.{u, u + 1} A L).hom ≫
      ((SSet.uliftFunctor.{u + 1, u}).obj A ◁
        joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) := by
  have hn : (SSet.uliftFunctor.{u + 1, u}).map (A ◁ joinInl L (Δ[0] : SSet.{u})) ≫
      (HomotopyLimits.uliftTensorIso.{u, u + 1} A (join L Δ[0])).hom =
    (HomotopyLimits.uliftTensorIso.{u, u + 1} A L).hom ≫
      ((SSet.uliftFunctor.{u + 1, u}).obj A ◁
        (SSet.uliftFunctor.{u + 1, u}).map (joinInl L Δ[0])) := rfl
  rw [coneTensorOldUniverseShape, ← Category.assoc, hn, Category.assoc,
    ← whiskerLeft_comp, uliftCoconeShapeIso_inl]
/-- 概要：元の全包含を宇宙比較が保持。
方針：積と余錐の自然性。規約：全射の等号。使われ方：両全境界の回収。 -/
lemma coneTensorLowerUniverseShape_boundary (A L : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u}) ▷ L) ≫
      coneTensorLowerUniverseShape A L =
    (HomotopyLimits.uliftTensorIso.{u, u + 1} A L).hom ≫
      (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
        (SSet.uliftFunctor.{u + 1, u}).obj L) := by
  have hn : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u}) ▷ L) ≫
      (HomotopyLimits.uliftTensorIso.{u, u + 1} (join A Δ[0]) L).hom =
    (HomotopyLimits.uliftTensorIso.{u, u + 1} A L).hom ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ▷
        (SSet.uliftFunctor.{u + 1, u}).obj L) := rfl
  rw [coneTensorLowerUniverseShape, ← Category.assoc, hn, Category.assoc,
    ← comp_whiskerRight, uliftCoconeShapeIso_inl]
/-- 概要：元の全包含を宇宙比較が保持。
方針：積と余錐の自然性。規約：全射の等号。使われ方：両全境界の回収。 -/
lemma coneTensorUniverseShape_old (A L : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (joinInl A (Δ[0] : SSet.{u}) ▷ join L Δ[0]) ≫ coneTensorUniverseShape A L =
    coneTensorOldUniverseShape A L ≫
      (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
        join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) := by
  have hn : (SSet.uliftFunctor.{u + 1, u}).map
      (joinInl A (Δ[0] : SSet.{u}) ▷ join L Δ[0]) ≫
      (HomotopyLimits.uliftTensorIso.{u, u + 1} (join A Δ[0]) (join L Δ[0])).hom =
    (HomotopyLimits.uliftTensorIso.{u, u + 1} A (join L Δ[0])).hom ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ▷
        (SSet.uliftFunctor.{u + 1, u}).obj (join L Δ[0])) := rfl
  rw [coneTensorUniverseShape, ← Category.assoc, hn]
  simp only [Category.assoc, coneTensorOldUniverseShape]
  apply (cancel_epi (HomotopyLimits.uliftTensorIso.{u, u + 1} A (join L Δ[0])).hom).mpr
  rw [← Category.assoc, ← comp_whiskerRight, uliftCoconeShapeIso_inl,
    whisker_exchange]
/-- 概要：元の全包含を宇宙比較が保持。
方針：積と余錐の自然性。規約：全射の等号。使われ方：両全境界の回収。 -/
lemma coneTensorUniverseShape_lower (A L : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (join A (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫ coneTensorUniverseShape A L =
    coneTensorLowerUniverseShape A L ≫
      (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ◁
        joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) := by
  have hn : (SSet.uliftFunctor.{u + 1, u}).map
      (join A (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫
      (HomotopyLimits.uliftTensorIso.{u, u + 1} (join A Δ[0]) (join L Δ[0])).hom =
    (HomotopyLimits.uliftTensorIso.{u, u + 1} (join A Δ[0]) L).hom ≫
      ((SSet.uliftFunctor.{u + 1, u}).obj (join A Δ[0]) ◁
        (SSet.uliftFunctor.{u + 1, u}).map (joinInl L Δ[0])) := rfl
  rw [coneTensorUniverseShape, ← Category.assoc, hn]
  simp only [Category.assoc, coneTensorLowerUniverseShape]
  apply (cancel_epi (HomotopyLimits.uliftTensorIso.{u, u + 1} (join A Δ[0]) L).hom).mpr
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    ← whiskerLeft_comp, uliftCoconeShapeIso_inl]
end SerrePositivity.InfinityCategories.F2.Ind
