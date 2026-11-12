module

public import SerrePositivity.KST.Spectra.PathContraction
public import SerrePositivity.KST.Comparison.BasedPathEndpoint

/-!
概要：path の収縮の終点は、元の path の時刻変数での評価である。
方針：終点の通常の指数評価の式を再利用し、区間の収縮を終点一で計算する。
規約：始点は零。時刻零が定数 path、時刻一が元の path。
使われ方：Goerss–Jardine I §7–8。零 loop 同値と円の成分表示の向きの照合。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 終点で path を収縮すると、元の path を収縮の時刻で評価する。 -/
@[reassoc]
lemma pathContraction_endpoint (Y : PointedSimplicialSet.{u}) :
    pathContraction Y ≫ (pathEndpoint Y).right =
      (β_ (basedPathSpace Y).right (Δ[1] : SSet.{u})).hom ≫ pathEvaluation Y := by
  rw [Comparison.basedPathEndpoint_evaluation, ← Category.assoc, pathContraction,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, KanPath.evaluation, ← Category.assoc,
    curry_pre_app, KanPath.curry_unit_evaluation]
  change (λ_ ((basedPathSpace Y).right ⊗ (Δ[1] : SSet.{u}))).inv ≫
    KanPath.endpoint 1 ▷ ((basedPathSpace Y).right ⊗ (Δ[1] : SSet.{u})) ≫
      pathReparametrization (basedPathSpace Y).right ≫ pathEvaluation Y = _
  have h : (λ_ ((basedPathSpace Y).right ⊗ (Δ[1] : SSet.{u}))).inv ≫
      KanPath.endpoint 1 ▷ ((basedPathSpace Y).right ⊗ (Δ[1] : SSet.{u})) ≫
        pathReparametrization (basedPathSpace Y).right =
      (β_ (basedPathSpace Y).right (Δ[1] : SSet.{u})).hom := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      change (if _ then (0 : Fin 2) else 1) = _
      split_ifs with h
      · exact h.symm
      · apply Fin.ext
        change 1 = ((stdSimplex.objEquiv s.2).toOrderHom j).val
        have hi : ((stdSimplex.objEquiv s.2).toOrderHom j).val < 2 :=
          ((stdSimplex.objEquiv s.2).toOrderHom j).isLt
        have hz : ((stdSimplex.objEquiv s.2).toOrderHom j).val ≠ 0 := by
          intro hz
          exact h (Fin.ext hz)
        omega
    · rfl
  simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ pathEvaluation Y) h

end
end SerrePositivity.KST.Spectra
