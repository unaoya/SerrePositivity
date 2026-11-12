module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ComposableHomotopyHorn
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.HomotopyTriangleComposite
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeHomotopyTriangleFilling

/-!
概要：指定部分三角形の長辺を境界円柱として厳密に保持するホモトピー合成。
方針：元の二円柱と部分三角形を固定して充填し、その長辺を取る。
規約：合成円柱の指定部分への制限を全単体で返す。
使われ方：近似・輸送・反映の相対比較円柱の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：指定された部分三角形の長辺を、全時刻で厳密に保持する合成円柱。
方針：相対ホーン充填と元の長辺の評価を合成する。
規約：境界の三角形は実際の射として指定する。使われ方：境界輸送を保つ比較合成。 -/
lemma exists_relativeHomotopyComposite {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) {f₀ f₁ f₂ : K ⟶ X}
    (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy f₁ f₂)
    (b : (Δ[2] : SSet.{u}) ⊗ (A : SSet.{u}) ⟶ X)
    (hb₀ : (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h)
    (hb₁ : (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h) :
    ∃ T : SSet.Homotopy f₀ f₂,
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h =
        (β_ (A : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
          (stdSimplex.δ (1 : Fin 3) ▷ (A : SSet.{u})) ≫ b := by
  obtain ⟨F, hF, hA⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyTriangle A U V b hb₀ hb₁
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.homotopyTriangleComposite U V F hF, ?_⟩
  change (β_ (A : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    (stdSimplex.δ (1 : Fin 3) ▷ (A : SSet.{u})) ≫ (((Δ[2] : SSet.{u}) ◁ A.ι) ≫ F) = _
  rw [hA]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
