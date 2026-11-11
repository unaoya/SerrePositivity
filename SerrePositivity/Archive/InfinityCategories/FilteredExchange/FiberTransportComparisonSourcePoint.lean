module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportComparisonSourceRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の輸送比較の初期係数制限と一点制限の順序を、指定値を保って交換する。
方針：同じ実二 prism の初期値制限と、二段の前合成の合成則を使う。
規約：元の比較を保持。使われ方：元の全初期値 q 上で区間比較を合成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の輸送の初期値制限の一点終点は、同じ初期値射による元の一点終点の前合成。 -/
lemma fiberTransportFamily_precomposeSource_point_endpoint {E B K K' L : SSet.{u}}
    (p : E ⟶ B) {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (T : FiberTransportFamily (b := b) p f γ) (r : K' ⟶ K) (l : L _⦋0⦌) :
    lift (𝟙 K') (SSet.const l) ≫ (T.precomposeSource r).endpoint =
      r ≫ lift (𝟙 K) (SSet.const l) ≫ T.endpoint := by
  change lift (𝟙 K') (SSet.const l) ≫ (r ▷ L) ≫ T.endpoint = _
  have hj : lift (𝟙 K') (SSet.const l) ≫ (r ▷ L) =
      r ≫ lift (𝟙 K) (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  rw [← Category.assoc, hj, Category.assoc]

/-- 元の指定比較の全初期値・一点制限は、初期値制限後の同じ指定比較の一点制限。 -/
lemma fiberTransportFamily_endpointIso_precomposeSource_point {E B K K' L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U : FiberTransportFamily (b := b) p f γ) (r : K' ⟶ K) (l : L _⦋0⦌) :
    HEq ((T.endpointIso p f γ h₁ U).precomp (lift r (SSet.const l)))
      (((T.precomposeSource r).endpointIso p (r ≫ f) γ h₁
        (U.precomposeSource r)).precomp (lift (𝟙 K') (SSet.const l))) := by
  let e := T.endpointIso p f γ h₁ U
  let j := lift (𝟙 K') (SSet.const l)
  have hj : j ≫ (r ▷ L) = lift r (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  have he := functorIso_precomp_heq_of_map_eq e hj.symm
  have ht := functorIso_precomp_precomp e (r ▷ L) j
  have hs := fiberTransportFamily_endpointIso_precomposeSource p f γ h₁ T U r
  exact he.trans ((heq_of_eq ht.symm).trans (heq_of_eq
    (congrArg (fun v => FunctorIso.precomp v j) hs)))

end SerrePositivity.InfinityCategories.F2
