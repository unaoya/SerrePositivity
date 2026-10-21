module
public import SerrePositivity.KST.SConstruction.CubicalLambdaTensorMap

/-! # Λ の実 oplax tensor 成分の入力自然性
概要：元の二写像を束ねる dg 関手は、全入力の前後合成について厳密に自然。
方針：元の Serre 対角の自然性と全 Hom の入力合成の回収式を使う。
規約：元の直積の両射影を保持。使われ方：Prop.4.6 の oplax tensor の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj
variable (A : Type u) [CommRing A]

/-- 全入力の合成の Hom 作用は、元の二つの Hom 作用の合成そのもの。 -/
lemma cubicalLambdaMap_comp_map {K L M : SSet.{u}} (a : K ⟶ L) (b : L ⟶ M)
    (x y : CubicalLambda A K) :
    (cubicalLambdaMap A (a ≫ b)).map x y = (cubicalLambdaMap A a).map x y ≫
      (cubicalLambdaMap A b).map ((cubicalLambdaMap A a).obj x)
        ((cubicalLambdaMap A a).obj y) :=
  (congrArg (cubicalSerreChains A).map (necklaceCubicalMap_comp a b x y)).trans
    ((cubicalSerreChains A).map_comp _ _)

/-- 元の二つの入力を束ねる実 dg 関手は、元の全前合成について厳密に自然。 -/
lemma cubicalLambdaTensorPair_precompose {M' M K L : SSet.{u}}
    (h : M' ⟶ M) (a : M ⟶ K) (b : M ⟶ L) :
    DGFunctor.comp (cubicalLambdaMap A h) (cubicalLambdaTensorPair A a b) =
      cubicalLambdaTensorPair A (h ≫ a) (h ≫ b) := by
  refine EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (cubicalLambdaMap A h) (cubicalLambdaTensorPair A a b))
    (G := cubicalLambdaTensorPair A (h ≫ a) (h ≫ b)) (fun _ => rfl) ?_
  intro x y
  have ht := comonoidPair_precompose (cubicalLambdaMapComonoid A h x y)
    ((cubicalLambdaMap A a).map ((cubicalLambdaMap A h).obj x) ((cubicalLambdaMap A h).obj y))
    ((cubicalLambdaMap A b).map ((cubicalLambdaMap A h).obj x) ((cubicalLambdaMap A h).obj y))
  have hs := congrArg₂ (fun f g => f ⊗ₘ g)
    (cubicalLambdaMap_comp_map A h a x y).symm (cubicalLambdaMap_comp_map A h b x y).symm
  exact (Category.comp_id _).trans
    (ht.trans (congrArg (fun f => Δ[x ⟶[Complex A] y] ≫ f) hs))

/-- 元の二つの入力を束ねる実 dg 関手は、元の全後合成について厳密に自然。 -/
lemma cubicalLambdaTensorPair_postcompose {M K L K' L' : SSet.{u}}
    (a : M ⟶ K) (b : M ⟶ L) (f : K ⟶ K') (g : L ⟶ L') :
    DGFunctor.comp (cubicalLambdaTensorPair A a b)
        (dgTensorFunctor A (cubicalLambdaMap A f) (cubicalLambdaMap A g)) =
      cubicalLambdaTensorPair A (a ≫ f) (b ≫ g) := by
  refine EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (cubicalLambdaTensorPair A a b)
      (dgTensorFunctor A (cubicalLambdaMap A f) (cubicalLambdaMap A g)))
    (G := cubicalLambdaTensorPair A (a ≫ f) (b ≫ g)) (fun _ => rfl) ?_
  intro x y
  have ht := tensorHom_comp_tensorHom
    ((cubicalLambdaMap A a).map x y) ((cubicalLambdaMap A b).map x y)
    ((cubicalLambdaMap A f).map ((cubicalLambdaMap A a).obj x) ((cubicalLambdaMap A a).obj y))
    ((cubicalLambdaMap A g).map ((cubicalLambdaMap A b).obj x) ((cubicalLambdaMap A b).obj y))
  have hs := congrArg₂ (fun c d => c ⊗ₘ d)
    (cubicalLambdaMap_comp_map A a f x y).symm (cubicalLambdaMap_comp_map A b g x y).symm
  exact (Category.comp_id _).trans ((Category.assoc _ _ _).trans
    (congrArg (fun c => Δ[x ⟶[Complex A] y] ≫ c) (ht.trans hs)))

/-- 元の直積の実 oplax tensor 成分は、元の両入力写像について厳密に自然。 -/
lemma cubicalLambdaOplaxTensor_naturality {K L K' L' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') :
    DGFunctor.comp (cubicalLambdaMap A (prod.map f g)) (cubicalLambdaOplaxTensor A K' L') =
      DGFunctor.comp (cubicalLambdaOplaxTensor A K L)
        (dgTensorFunctor A (cubicalLambdaMap A f) (cubicalLambdaMap A g)) := by
  have hp := cubicalLambdaTensorPair_precompose A (prod.map f g)
    (prod.fst : K' ⨯ L' ⟶ K') (prod.snd : K' ⨯ L' ⟶ L')
  have hq := cubicalLambdaTensorPair_postcompose A
    (prod.fst : K ⨯ L ⟶ K) (prod.snd : K ⨯ L ⟶ L) f g
  have hr := congrArg₂ (fun a b => cubicalLambdaTensorPair A a b)
    (prod.map_fst f g) (prod.map_snd f g)
  exact hp.trans (hr.trans hq.symm)

end SerrePositivity.KST.SConstruction
