module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCornerTarget
public import SerrePositivity.InfinityCategories.F2.Ind.IndCommaRelativeCocone

/-!
概要：元の scalar comma の全余錐積拡張を、終点面の指定変換を保って選び直す。
方針：補間領域の指定部分で相対余錐を取り、同じ全積へ戻す。
規約：旧族と下方余錐の両全境界、元の指定変換を保持する。
使われ方：有限半順序形状の新しい極大点評価下の実余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：同じ全拡張の両境界と終点面の指定下側変換を同時に保持する。
方針：小さい補間領域の相対余錐。規約：全射の等号。使われ方：極大点評価の補間。 -/
lemma exists_indComma_coneTensor_relative_extension (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C A L B : SSet.{u}} [Quasicategory C] (x : (IndInfinity κ C) _⦋0⦌)
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L) (hB : IsKappaSmall κ B)
    (E : join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ⊗
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶ leftKanShape (indYoneda κ C) x)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ leftKanShape (indYoneda κ C) x)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ≫
      tensorRightPoint (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0])
        (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E =
      t ≫ sliceUnderProjection z) :
    ∃ (E' : join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ⊗
        join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶ leftKanShape (indYoneda κ C) x)
      (d : JoinCocone t),
      (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
        join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E' =
      (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
        join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E ∧
      (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ◁
        joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E' =
      (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ◁
        joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E ∧
      tensorRightPoint (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0])
        (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E' =
      d.val ≫ sliceUnderProjection z := by
  let H := (SSet.uliftFunctor.{u + 1, u}).map (coneTensorCornerInclusion A L) ≫
    coneTensorUniverseShape A L ≫ E
  obtain ⟨c, d, hd⟩ := exists_indComma_relative_cocones κ x (coneTensorTargetInclusion A L)
    hA (coneTensorCorner_isKappaSmall (Fact.out : κ.IsRegular) hA hL) hB H z t
    ((coneTensorCorner_target E).trans ht)
  refine ⟨inv (coneTensorUniverseShape A L) ≫ coneTensorExtend c, d,
    coneTensorNativeExtend_old E c, coneTensorNativeExtend_lower E c, ?_⟩
  rw [coneTensorNativeExtend_target]
  exact hd.symm
end SerrePositivity.InfinityCategories.F2.Ind
