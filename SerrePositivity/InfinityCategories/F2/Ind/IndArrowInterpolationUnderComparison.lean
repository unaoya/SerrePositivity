module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCommaComparison
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationOldFamilySourceIso
/-!
概要：元の補間旧族と q の指定始点比較を、同じ下側変換の実 under comma へ戻す。
方針：始点評価が等号となる同じ comma 同型と、下側変換の恒等同型を束ねる。
規約：元の両全族と指定変換を保持し、追加の Kan 性を要求しない。
使われ方：始点評価下での補間余錐の元の試験族への輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A L : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
local notation "E" => diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
variable (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
  leftKanShape (indYoneda κ C)
    (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))
  (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
  (ht : q ≫ diagramCommaEvaluation κ D
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = t ≫ sliceUnderProjection z)
/-- 概要：指定下側変換を保持する実 under comma 内で、元の旧族と q は同型。
方針：同じ始点評価整合付き同型を二成分の比較へ適用する。
規約：全パラメーターを保持。使われ方：元の試験族への相対余錐の帰還。 -/
lemma nonempty_indArrowInterpolationOldFamily_under_iso :
    Nonempty (FunctorIso
      (relativeCommaFamily E z t (indArrowInterpolationOldFamily V)
        ((indArrowInterpolationOldFamily_source V).trans ht))
      (relativeCommaFamily E z t q ht)) := by
  obtain ⟨d, hd⟩ := exists_indArrowInterpolationOldFamily_iso_source V
  exact nonempty_relativeCommaFamily_iso E z _ q t _ ht d hd
end SerrePositivity.InfinityCategories.F2.Ind
