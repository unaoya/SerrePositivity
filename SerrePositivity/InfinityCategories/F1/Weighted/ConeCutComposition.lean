module

public import SerrePositivity.InfinityCategories.F1.Coherent.PathCutMinimumComposition
public import SerrePositivity.InfinityCategories.Core.PrismOpposite

/-!
概要：時間切断の座標から、weighted cone の時刻一側の実際の Hom 係数を作る。
方針：元の係数と切断後の変換係数を豊穣合成し、終点で元の係数の合成を回収する。
規約：豊穣圏の局所 Kan 性は要求しない。時間切断を端点だけへ制限しない。
使われ方：weighted pointed prism の初点から正頂点への非定値 Hom。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 反転した二つの係数の合成を戻すと、元の二つの係数の同時評価の合成になる。 -/
lemma reflectedSimplexMap_compLift {A B X : SSet.{u}} {n : ℕ}
    (a : Δ[n] ⟶ A.op) (b : Δ[n] ⟶ B.op) (f : A ⊗ B ⟶ X) :
    reflectedSimplexMap (lift a b ≫ (opTensorIso A B).hom ≫ SSet.opFunctor.map f) =
      lift (reflectedSimplexMap a) (reflectedSimplexMap b) ≫ f := by
  apply SSet.hom_ext
  intro d
  rfl

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 正頂点までの元の係数と、同じ初区間へ制限した変換係数を反転側で合成する。 -/
def weightedCutCompositeSimplex (x y z : C) {n : ℕ} (j : Fin (n + 1))
    (τ : (Δ[j.val] : SSet.{u}) ⟶ (SimplicialCategory.sHom x y).op)
    (η : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom y z).op) :
    (Δ[j.val] : SSet.{u}) ⟶ (SimplicialCategory.sHom x z).op :=
  lift τ (stdSimplex.map (simplexPrefixInclusion j.val n (by omega)) ≫ η) ≫
    (opTensorIso _ _).hom ≫ SSet.opFunctor.map (eComp SSet x y z)

/-- 時刻一の正頂点への係数は、最初の正頂点と最初の時刻一の点の同時評価。 -/
def weightedConeCutCoefficient (x y z : C) {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (j : Fin (n + 1)) (hj : t j = 1)
    (τ : (Δ[j.val] : SSet.{u}) ⟶ (SimplicialCategory.sHom x y).op)
    (η : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom y z).op) :
    nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      SimplicialCategory.sHom x z :=
  lift (pathFirstMinimumMap j ≫ reflectedSimplexMap τ)
    (pathCutMinimumMap t hj ≫ reflectedSimplexMap η) ≫ eComp SSet x y z

/-- 時刻一の端点では、全ての path 上で元の weighted 係数の合成に厳密に一致。 -/
lemma weightedConeCutCoefficient_one (x y z : C) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (ht : ∀ k, t k = 1) (j : Fin (n + 1))
    (τ : (Δ[j.val] : SSet.{u}) ⟶ (SimplicialCategory.sHom x y).op)
    (η : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom y z).op) :
    weightedConeCutCoefficient x y z t j (ht j) τ η =
      pathFirstMinimumMap j ≫ reflectedSimplexMap (weightedCutCompositeSimplex x y z j τ η) := by
  rw [weightedConeCutCoefficient, pathCutMinimumMap_eq_firstMinimum t ht,
    weightedCutCompositeSimplex, reflectedSimplexMap_compLift, reflectedSimplexMap_pre]
  have h := comp_lift (pathFirstMinimumMap j) (reflectedSimplexMap τ)
    (SSet.opFunctor.map (stdSimplex.map (simplexPrefixInclusion j.val n (by omega))) ≫
      reflectedSimplexMap η)
  simpa only [Category.assoc] using
    (congrArg (fun f => f ≫ eComp SSet x y z) h).symm

/-- 全時間パラメーターを持つ cone の係数は、面・退化への制限と厳密に可換。 -/
lemma weightedConeCutCoefficient_reindex (x y z : C) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (t : Fin (n + 1) →o Fin 2) (j : Fin (m + 1))
    (hj : t (α.toOrderHom j) = 1)
    (τ : (Δ[(α.toOrderHom j).val] : SSet.{u}) ⟶ (SimplicialCategory.sHom x y).op)
    (η : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom y z).op) :
    nerveMap (pathFirstReindexFunctor α.toOrderHom j) ≫
      weightedConeCutCoefficient x y z t (α.toOrderHom j) hj τ η =
    weightedConeCutCoefficient x y z (t.comp α.toOrderHom) j hj
      (stdSimplex.map (simplexPrefixRestriction α j) ≫ τ) (stdSimplex.map α ≫ η) := by
  simp only [weightedConeCutCoefficient, reflectedSimplexMap_pre]
  have h := comp_lift (nerveMap (pathFirstReindexFunctor α.toOrderHom j))
    (pathFirstMinimumMap (α.toOrderHom j) ≫ reflectedSimplexMap τ)
    (pathCutMinimumMap t hj ≫ reflectedSimplexMap η)
  have h' := congrArg (fun f => f ≫ eComp SSet x y z) h
  simp only [Category.assoc] at h'
  rw [h', ← Category.assoc _ (pathFirstMinimumMap _), pathFirstMinimumMap_reindex,
    ← Category.assoc _ (pathCutMinimumMap t hj), pathCutMinimumMap_reindex]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories
