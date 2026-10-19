module
public import SerrePositivity.KST.SConstruction.ArCutEvaluation

/-! # 切断位置を含む単体作用素の自然性
概要：任意の単調写像は切断位置も写すと切断四角形の全単体と可換になる。
方針：全順序の単調写像による min・max の保存を四隅で使う。
規約：単射性を仮定せず退化も含む。使われ方：切断比較の面・退化の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 任意の単調写像は切断端点の四角形と厳密に可換。 -/
lemma cutEndpoint_naturality {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (k i : Fin (m + 1)) (x y : Fin 2) :
    θ (cutEndpoint k i x y) = cutEndpoint (θ k) (θ i) x y := by
  fin_cases x <;> fin_cases y
  · exact (congrArg θ (cutEndpoint_zero_zero k i)).trans
      (θ.monotone.map_min.trans (cutEndpoint_zero_zero (θ k) (θ i)).symm)
  · exact (congrArg θ (cutEndpoint_zero_one k i)).trans
      (cutEndpoint_zero_one (θ k) (θ i)).symm
  · exact (congrArg θ (cutEndpoint_one_zero k i)).trans
      (cutEndpoint_one_zero (θ k) (θ i)).symm
  · exact (congrArg θ (cutEndpoint_one_one k i)).trans
      (θ.monotone.map_max.trans (cutEndpoint_one_one (θ k) (θ i)).symm)

/-- 任意の切断角の端点制限は切断位置も含めた単調写像に関して自然。 -/
lemma cutCornerOrder_naturality {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (k : Fin (m + 1)) (x y : Fin 2) :
    (cutCornerOrder (θ k) x y).comp θ = θ.comp (cutCornerOrder k x y) :=
  DFunLike.ext _ _ (fun i => (cutEndpoint_naturality θ k i x y).symm)

/-- 切断四角形の族は切断位置を写す任意の単体作用素と全高次単体で厳密に可換。 -/
lemma arCutSquareMap_naturality {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (k : Fin (m + 1)) :
    (arNerveMap θ ⊗ₘ 𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ arCutSquareMap n (θ k) =
      arCutSquareMap m k ≫ arNerveMap θ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (cutEndpoint_naturality θ k (s.1.obj r).down.val.1
      (prodStdSimplex.objEquiv s.2 r).1 (prodStdSimplex.objEquiv s.2 r).2).symm
  · exact (cutEndpoint_naturality θ k (s.1.obj r).down.val.2
      (prodStdSimplex.objEquiv s.2 r).1 (prodStdSimplex.objEquiv s.2 r).2).symm

end SerrePositivity.KST.SConstruction
