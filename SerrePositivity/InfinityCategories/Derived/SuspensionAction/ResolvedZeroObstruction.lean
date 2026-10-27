module
public import SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.CellZeroObstruction
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.SphereConeData

/-!
概要：工程 1 の dg 関手という供給型を、実際の新 cone へ特殊化して検証する。
方針：零 dg 入力を取り、新 sphere 閉包の零対象で関手族を評価する。
規約：dg 関手圏間の dg 作用を否定する。native SSet 射や最終 map の非存在は主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.NonConnective
open DGCategoryCellResolution
variable (R : Type u) [CommRing R] [Nontrivial R]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
/-- 新 cone の固定分解を保った resolvedInputFunctor の dg 供給型は、零入力で不可能。 -/
theorem no_dgSphereClosureResolvedInputFunctor :
    ¬ Nonempty (DGFunctor R (DGFunctor R CellZeroInput.{v} CellZeroInput.{v})
      (DGFunctor R
        (Source R (DGKappaCone R CellZeroInput.{v}
          (dgKappaConeInput_unconditional' R CellZeroInput.{v} κ hκ)))
        (Source R (DGKappaCone R CellZeroInput.{v}
          (dgKappaConeInput_unconditional' R CellZeroInput.{v} κ hκ))))) := by
  let I := dgKappaConeInput_unconditional' R CellZeroInput.{v} κ hκ
  let C := DGKappaCone R CellZeroInput.{v} I
  let zero : C := ⟨moduleZero R CellZeroInput.{v},
    dgKappaSphereClosureObjects_zero R CellZeroInput.{v} hκ⟩
  exact no_dgZeroInputFamily R C (Source R C) ⟨zero⟩

end SerrePositivity.InfinityCategories
