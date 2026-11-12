module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.HornOneLastPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeHornTensorExtension

/-!
概要：終点の全体射を固定して、指定された境界ホモトピーを全体へ延長する。
方針：最後の一次ホーンと部分複体の積の和に沿って Kan 標的へ延長する。
規約：境界の全円柱と終点を厳密に保持。使われ方：相対持ち上げの境界の厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：指定境界円柱は、終点を全体で固定したまま全体円柱へ延長できる。
方針：一次外ホーンの相対充填。規約：有限性不要。使われ方：境界の元の始点への補正。 -/
lemma kanComplex_extend_boundary_homotopy_final {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) (r : K ⟶ X) (a : (A : SSet.{u}) ⟶ X)
    (L : SSet.Homotopy a (A.ι ≫ r)) :
    ∃ r' : K ⟶ X, A.ι ≫ r' = a ∧ ∃ S : SSet.Homotopy r' r,
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ S.h = L.h := by
  let b := (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫ L.h
  let c := snd (horn 1 1 : SSet.{u}) K ≫ r
  have h : ((horn 1 1).ι ▷ (A : SSet.{u})) ≫ b =
      ((horn 1 1 : SSet.{u}) ◁ A.ι) ≫ c := by
    dsimp only [b, c]
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.hornOneLast_prism_factorization, Category.assoc]
    change snd (horn 1 1 : SSet.{u}) (A : SSet.{u}) ≫ SSet.ι₁ ≫ L.h = _
    rw [L.h₁]
    rfl
  obtain ⟨F, hF, hA⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHornTensorExtension A (1 : Fin 2) c b h
  change ((horn 1 1).ι ▷ K) ≫ F = c at hF
  change ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ F = b at hA
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ F = r := by
    have h' := congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneLastSection K ≫ t) hF
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneLastSection_ι, c,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneLastSection_snd, Category.id_comp] using h'
  let r' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ F
  have hr' : A.ι ≫ r' = a := by
    change A.ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ F = a
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 0 A.ι, Category.assoc, hA]
    exact L.h₀
  let S : SSet.Homotopy r' r :=
    { h := (β_ K (Δ[1] : SSet.{u})).hom ≫ F
      h₀ := by rfl
      h₁ := h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  refine ⟨r', hr', S, ?_⟩
  change (β_ (A : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    (((Δ[1] : SSet.{u}) ◁ A.ι) ≫ F) = L.h
  rw [hA]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
