module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
概要：任意のホーンのパラメータ付き充填を、指定部分上で厳密に固定する。
方針：ホーンと部分複体の積の和に沿う Kan 延長。
規約：外ホーンも含む。使われ方：相対比較円柱の合成と反転。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元のホーンと指定部分単体を同時に保つ充填。
方針：積の和を貼って anodyne 延長。規約：有限性不要。使われ方：相対二次ホーン。 -/
lemma exists_relativeHornTensorExtension {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) {n : ℕ} (i : Fin (n + 2))
    (a : (horn (n + 1) i : SSet.{u}) ⊗ K ⟶ X)
    (b : (Δ[n + 1] : SSet.{u}) ⊗ (A : SSet.{u}) ⟶ X)
    (h : ((horn (n + 1) i).ι ▷ (A : SSet.{u})) ≫ b =
      ((horn (n + 1) i : SSet.{u}) ◁ A.ι) ≫ a) :
    ∃ F : (Δ[n + 1] : SSet.{u}) ⊗ K ⟶ X,
      ((horn (n + 1) i).ι ▷ K) ≫ F = a ∧
        ((Δ[n + 1] : SSet.{u}) ◁ A.ι) ≫ F = b := by
  let P := Subcomplex.unionProd.isPushout (horn (n + 1) i) A
  let c := P.desc b a h
  have hi := anodyneExtensions_unionProd_ι' (horn (n + 1) i) A
    (anodyneExtensions.horn_ι i)
  have := hi (terminal.from X)
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  have sq : CommSq c (Subcomplex.unionProd (horn (n + 1) i) A).ι (terminal.from X)
      (terminal.from ((Δ[n + 1] : SSet.{u}) ⊗ K)) := ⟨terminalIsTerminal.hom_ext _ _⟩
  refine ⟨sq.lift, ?_, ?_⟩
  · rw [← Subcomplex.unionProd.ι₂_ι (horn (n + 1) i) A, Category.assoc, sq.fac_left]
    exact P.inr_desc _ _ _
  · rw [← Subcomplex.unionProd.ι₁_ι (horn (n + 1) i) A, Category.assoc, sq.fac_left]
    exact P.inl_desc _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
