module
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.Stable.LeftFibrationInitialPiZero
public import SerrePositivity.InfinityCategories.Stable.SquareHomotopyCategory

/-! # 余極限余錐の固定終点空間と Hom

概要：余極限余錐の頂点から指定頂点への Hom は、固定終点余錐空間の π₀ と同値である。
方針：余極限性を coslice の始対象性として left fibration の比較に適用する。
規約：追加の安定性は不要。使われ方：suspension の二枝交換と写像空間のループの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：終点固定の余錐の連結成分は余極限頂点からの Hom と同値。
方針：coslice 射影の始対象を持つ left fibration としての比較を使う。
規約：図式の形状は任意。使われ方：余錐空間の π₀ の表現可能性。 -/
def coconeMappingSpacePiZeroEquiv {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) (y : X _⦋0⦌) :
    SSet.π₀ (coconeMappingSpace p y) ≃
      ((SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :=
  leftFibrationInitialFiberPiZeroEquiv (sliceUnderProjection p) c hc y

/-- 概要：押し出し四角形の標準余錐の頂点は元の右上の頂点。
方針：余錐頂点を第一三角形の最終頂点として比較する。
規約：値域の仮定なし。使われ方：余錐空間の Hom の終域表示。 -/
lemma pushoutCocone_vertex {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (pushoutCocone R).vertex = squareVertex R 1 1 := by
  have hL := spanCoconeSquareIso_left.{u}
  change (joinStdSimplexIso 1 0).inv ≫
    (joinMap horn₂₀.ι₀₁ (𝟙 (Δ[0] : SSet.{u})) ≫ spanCoconeSquareIso.hom) =
      squareTriangle 1 at hL
  have hh := congrArg (fun q => (joinStdSimplexIso 1 0).hom ≫ q) hL
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hh
  have hj : joinInr (horn 2 0 : SSet.{u}) Δ[0] ≫ spanCoconeSquareIso.hom =
      stdSimplex.map (PinchedHom.lastVertex 1) ≫ squareTriangle 1 := by
    calc
      _ = joinInr Δ[1] Δ[0] ≫
          (joinMap horn₂₀.ι₀₁ (𝟙 (Δ[0] : SSet.{u})) ≫ spanCoconeSquareIso.hom) := by
        simp only [← Category.assoc, joinInr_joinMap, Category.id_comp]
      _ = _ := by rw [hh, ← Category.assoc, joinStdSimplexIso_rightPoint_inr]
  change SSet.yonedaEquiv (joinInr (horn 2 0 : SSet.{u}) Δ[0] ≫
    (spanCoconeSquareIso.hom ≫ R)) = _
  rw [← Category.assoc, hj, Category.assoc, SSet.yonedaEquiv_comp]
  apply congrArg (fun v => R.app (Opposite.op ⦋0⦌) v)
  apply Prod.ext <;> decide

/-- 概要：押し出しの入力 span の余錐空間の π₀ は終端頂点からの Hom と同値。
方針：四角形の標準余錐に一般の余極限の比較を適用する。
規約：安定性・零角は不要。使われ方：suspension 四角形の頂点からの射の表示。 -/
def pushoutCoconeMappingSpacePiZeroEquiv {X : SSet.{u}} [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R) (y : X _⦋0⦌) :
    SSet.π₀ (coconeMappingSpace (pushoutSpan R) y) ≃
      ((squareHoVertex R 1 1 : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) := by
  have h := coconeMappingSpacePiZeroEquiv (pushoutCocone R) hR y
  rw [pushoutCocone_vertex] at h
  exact h

end SerrePositivity.InfinityCategories
