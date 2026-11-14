module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.UliftPointTensorEvaluation

/-!
概要：ULiftで持ち上げた点の評価を、元の第0単体の評価へ戻す。
方針：第0単体の一意性と第一射影の逆則を使う。
規約：IS-W2 C01の既存構成の単位・係数移送則。
使われ方：HA 1.2.4、元のTot錐の脚を第0単体で読む。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open scoped Simplicial

/-- 同じ点と評価を任意単体で読むと、同じ元の評価のULiftになる。 -/
theorem uliftPointSimplexEvaluation (K E Q : SSet.{u})
    (p : (Δ[0] : SSet.{u}) ⟶ E) (f : K ⊗ E ⟶ Q)
    {n : ℕ} (σ : K _⦋n⦌) (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    let U := SSet.uliftFunctor.{v,u}
    let e := (uliftStdSimplexIso.{u,v} 0).inv ≫ U.map p
    let s := inv (fst (U.obj K) (Δ[0] : SSet.{max u v})) ≫
      (U.obj K ◁ e) ≫ (uliftTensorIso K E).inv ≫ U.map f
    s.app (Opposite.op ⦋n⦌) (ULift.up σ) =
      ULift.up (f.app (Opposite.op ⦋n⦌)
        (σ, p.app (Opposite.op ⦋n⦌) a₀)) := by
  dsimp only
  let τ : ((SSet.uliftFunctor.{v,u}).obj K) _⦋n⦌ := ULift.up σ
  let b := (inv (fst ((SSet.uliftFunctor.{v,u}).obj K)
    (Δ[0] : SSet.{max u v}))).app (Opposite.op ⦋n⦌) τ
  have hb := ConcreteCategory.congr_hom (NatTrans.congr_app (IsIso.inv_hom_id
    (fst ((SSet.uliftFunctor.{v,u}).obj K) (Δ[0] : SSet.{max u v})))
      (Opposite.op ⦋n⦌)) τ
  change b.1 = τ at hb
  let a := ((uliftStdSimplexIso.{u,v} 0).inv.app (Opposite.op ⦋n⦌) b.2).down
  have ha : a = a₀ := by
    apply SSet.stdSimplex.ext
    intro i
    change (_ : Fin 1) = (_ : Fin 1)
    exact Subsingleton.elim _ _
  change ULift.up (f.app (Opposite.op ⦋n⦌) (b.1.down, p.app _ a)) = _
  rw [hb, ha]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
