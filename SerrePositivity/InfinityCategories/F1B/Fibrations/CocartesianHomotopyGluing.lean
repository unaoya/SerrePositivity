module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianHornComparison
public import SerrePositivity.InfinityCategories.Core.CocartesianHomotopyExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct

/-!
概要：積の和上で cocartesian な輸送を貼り合わせる。
方針：curry した輸送を cocartesian path の全部分複体へ持ち上げ、その中で pushout を取る。
規約：時間が直積の左因子、貼り合わせる部分は二つの空間因子の部分複体。
使われ方：section の境界と始対象での評価を同時に固定する相対輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cocartesian な垂直辺を持つ輸送をその path の空間へ curry する。
方針：各頂点の辺の条件を全部分複体への持ち上げ条件へ直す。
規約：射影の充填性は不要。
使われ方：輸送の貼り合わせで辺の条件を保つ。 -/
def cocartesianHomotopyCurry {D E B : SSet.{u}} (p : E ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ D ⟶ E)
    (hH : ∀ x : D _⦋0⦌, HasCocartesianHornLifting p (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    D ⟶ cocartesianPathSpace p :=
  fullSubcomplexLift (IsCocartesianHornPathVertex p) (curry H) (by
    intro x
    unfold IsCocartesianHornPathVertex
    change HasCocartesianHornLifting p (edgeOfSimplex (intervalFunctorVertexEdge _))
    rw [intervalFunctorVertexEdge_curry]
    exact hH x)

/-- 概要：貼り合わせる二つの cocartesian な輸送は積の和全体の輸送を定める。
方針：cocartesian path の空間で貼り、uncurry して垂直辺の条件を回収する。
規約：重なりでの一致は厳密な射の等式。
使われ方：section の境界上の輸送と指定評価上の定値輸送の貼り合わせ。 -/
lemma exists_kanCocartesianHomotopy_unionProd {A T E B : SSet.{u}}
    (p : E ⟶ B) (S : A.Subcomplex) (U : T.Subcomplex)
    (H₁ : (Δ[1] : SSet.{u}) ⊗ (A ⊗ (U : SSet.{u})) ⟶ E)
    (H₂ : (Δ[1] : SSet.{u}) ⊗ ((S : SSet.{u}) ⊗ T) ⟶ E)
    (h : (Δ[1] ◁ (S.ι ▷ (U : SSet.{u}))) ≫ H₁ =
      (Δ[1] ◁ ((S : SSet.{u}) ◁ U.ι)) ≫ H₂)
    (h₁ : ∀ x : (A ⊗ (U : SSet.{u})) _⦋0⦌, HasCocartesianHornLifting p (edgeOfSimplex
      (H₁.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))))
    (h₂ : ∀ x : ((S : SSet.{u}) ⊗ T) _⦋0⦌, HasCocartesianHornLifting p (edgeOfSimplex
      (H₂.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ (Subcomplex.unionProd S U : SSet.{u}) ⟶ E,
      (Δ[1] ◁ Subcomplex.unionProd.ι₁ S U) ≫ H = H₁ ∧
      (Δ[1] ◁ Subcomplex.unionProd.ι₂ S U) ≫ H = H₂ ∧
      ∀ x : (Subcomplex.unionProd S U : SSet.{u}) _⦋0⦌,
        HasCocartesianHornLifting p (edgeOfSimplex
          (H.app (Opposite.op ⦋1⦌)
            (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
  let k₁ := cocartesianHomotopyCurry p H₁ h₁
  let k₂ := cocartesianHomotopyCurry p H₂ h₂
  have hk₁ : k₁ ≫ cocartesianPathSpaceι p = curry H₁ := fullSubcomplexLift_ι _ _ _
  have hk₂ : k₂ ≫ cocartesianPathSpaceι p = curry H₂ := fullSubcomplexLift_ι _ _ _
  have : Mono (cocartesianPathSpaceι p) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices _ (IsCocartesianHornPathVertex p)).ι)
  have he : (S.ι ▷ (U : SSet.{u})) ≫ k₁ = ((S : SSet.{u}) ◁ U.ι) ≫ k₂ := by
    apply (cancel_mono (cocartesianPathSpaceι p)).1
    rw [Category.assoc, hk₁, Category.assoc, hk₂]
    rw [← curry_natural_left, ← curry_natural_left, h]
  let q := Subcomplex.unionProd.isPushout S U
  let k := q.desc k₁ k₂ he
  let H := uncurry (k ≫ cocartesianPathSpaceι p)
  have hC : curry H = k ≫ cocartesianPathSpaceι p := curry_uncurry _
  refine ⟨H, ?_, ?_, ?_⟩
  · apply curry_injective
    rw [curry_natural_left, hC, ← Category.assoc]
    rw [q.inl_desc]
    exact hk₁
  · apply curry_injective
    rw [curry_natural_left, hC, ← Category.assoc]
    rw [q.inr_desc]
    exact hk₂
  · intro x
    have hx := fullSubcomplexOnVertices_vertex (k.app (Opposite.op ⦋0⦌) x)
    change IsCocartesianHornPathVertex p ((k ≫ cocartesianPathSpaceι p).app _ x) at hx
    rw [← hC] at hx
    unfold IsCocartesianHornPathVertex at hx
    change HasCocartesianHornLifting p (edgeOfSimplex (intervalFunctorVertexEdge _)) at hx
    rw [intervalFunctorVertexEdge_curry] at hx
    exact hx

end SerrePositivity.InfinityCategories
