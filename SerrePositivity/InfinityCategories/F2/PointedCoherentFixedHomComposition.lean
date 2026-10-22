module

public import SerrePositivity.InfinityCategories.F2.CosliceFixedHomComposition
public import SerrePositivity.InfinityCategories.F2.PointedCoherentCosliceFiber

/-!
概要：元の固定 Kan 射の全反転 Hom 作用を、実 pointed space の同じ係数作用へ戻す。
方針：全 coslice の固定射の合成則と、元の一点表示の厳密な正規化を合成する。
規約：元の Kan 射・全係数・元の標準 fiber 比較を保持する。
使われ方：三辺の実 pointed 族の native 値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の Kan 射を固定した全係数の合成は、実 pointed space でも同じ元の作用。 -/
lemma pointedCoherentSourcePrecomposition_fixed {K L : KanObject.{u}} (f : K ⟶ L) :
    lift (SSet.const
      ((coherentCosliceFiberComparison K L ≫ vertexFiberι
        (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)))
          (coherentNerveVertex L)).app (Opposite.op ⦋0⦌)
            (ULift.up (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' K L f)))))
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom pointKanObject K).op)) ≫
      coherentCosliceSourcePrecomposition pointKanObject K ≫ pointedCoherentCosliceIso.hom =
    (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)) ≫
        pointedCoherentFiberComparison L ≫
          vertexFiberι pointedSpaceProjection (coherentNerveVertex L) := by
  rw [← Category.assoc, coherentCosliceSourcePrecomposition_fixed]
  simp only [Category.assoc]
  rw [← pointedCoherentCosliceIso_comparison]

end SerrePositivity.InfinityCategories.F2
