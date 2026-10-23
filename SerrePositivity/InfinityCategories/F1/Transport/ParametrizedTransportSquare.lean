module

public import SerrePositivity.InfinityCategories.F1.Transport.FiberTransportSquare
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso

/-!
概要：底も動かす可換正方形に対する普遍輸送の全パラメーター付き自然性。
方針：元の普遍輸送を正方形で後合成し、同じ初期条件の標的の輸送族と比較する。
規約：写像空間への射を一つの関手同型で比較する。
使われ方：反対 nerve 上の同値性を実際の pointed-space 射影へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：可換正方形は普遍輸送と写像空間の後合成を関手同型まで可換にする。
方針：普遍族の後合成に任意の始点係数射の普遍比較を適用する。
規約：底・全空間・fiber の各射を厳密に保持する。
使われ方：普遍輸送の同値性を底と全空間の同型に沿って移す。 -/
def parametrizedFiberTransport_squareIso {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g) (a b : B _⦋0⦌) :
    FunctorIso
      (parametrizedFiberTransport p a b ≫
        (ihom (vertexFiber p a)).map (transportSquareFiberMap p q f g h b))
      (intervalMappingPost g a b ≫ parametrizedFiberTransport q (g.app _ a) (g.app _ b) ≫
        (pre (transportSquareFiberMap p q f g h a)).app (vertexFiber q (g.app _ b))) := by
  let U₀ := (parametrizedFiberTransportFamily p a b).pushforward p q f g h
  let k := transportSquareFiberMap p q f g h a
  let v := intervalMappingPost g a b
  let γ := intervalMappingUncurry v
  have hγ : γ = intervalMappingUncurry (𝟙 (intervalMappingSpace a b)) ≫ g :=
    intervalMappingPost_universal_uncurry g a b
  let U : FiberTransportFamily (b := g.app _ b) q k γ :=
    ⟨U₀.endpoint, U₀.prism, by simpa only [Category.id_comp] using U₀.start,
      U₀.finish, by rw [hγ]; exact U₀.over_base⟩
  have e := U.mapIso_parametrizedSource q k γ
    (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)
  have hv : intervalMappingCurryOfEndpoints γ
      (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v) = v := by
    apply intervalMappingUncurry_injective _ _
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hv] at e
  change FunctorIso U₀.map _ at e
  rw [FiberTransportFamily.pushforward_map] at e
  exact e

/-- 概要：底と全空間が同型の正方形は普遍輸送の同値性を保つ。
方針：自然性の関手同型で移し、パラメーターと両 fiber の同型を消去する。
規約：全写像空間に依存する普遍輸送についての主張。
使われ方：coherent nerve の反対の同型による pointed-space 輸送の回収。 -/
lemma parametrizedFiberTransport_isQCatEquivalence_of_squareIso
    {E B F D : SSet.{u}} (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    [Quasicategory B] [Quasicategory D] (e : E ≅ F) (d : B ≅ D)
    (h : e.hom ≫ q = p ≫ d.hom) (a b : B _⦋0⦌)
    (hp : IsQCatEquivalence (parametrizedFiberTransport p a b)) :
    IsQCatEquivalence (parametrizedFiberTransport q (d.hom.app _ a) (d.hom.app _ b)) := by
  have := transportSquareFiberMap_isIso p q e d h a
  have := transportSquareFiberMap_isIso p q e d h b
  let ea := qCatEquivalenceOfIso (asIso (transportSquareFiberMap p q e.hom d.hom h a))
  let eb := qCatEquivalenceOfIso (asIso (transportSquareFiberMap p q e.hom d.hom h b))
  have hs := ea.isQCatEquivalence
  have ht := eb.isQCatEquivalence
  have hc := (hp.comp (ht.postcompose _)).ofFunctorIso
    (parametrizedFiberTransport_squareIso p q e.hom d.hom h a b)
  have hb := (qCatEquivalenceOfIso (intervalMappingPostIso d a b)).isQCatEquivalence
  exact (hs.precompose _).cancel_right (hb.cancel_left hc)

end SerrePositivity.InfinityCategories
