module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ComposableHomotopyHorn
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.HomotopyTriangleComposite
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.QuasiHomotopyTriangle
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeHomotopyComposite

/-!
概要：元の quasicategory 内の境界輸送の合成と、その Kan 標的内の比較を同時に合成する。
方針：元の境界の合成三角形の像を標的の部分三角形として固定する。
規約：合成後も全境界円柱が元の像に厳密に一致。使われ方：一般の相対有限比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：境界内の二段の輸送と全体の比較を、元の像の全円柱を保持して合成できる。
方針：元の合成三角形を標的の相対充填に指定。
規約：始域は quasicategory、標的は Kan。使われ方：二入力還元と相対検出の接続。 -/
lemma exists_relativeHomotopyCompositionAlongMap {K X Y : SSet.{u}}
    [Quasicategory X] [KanComplex Y] (A : K.Subcomplex) (k : X ⟶ Y)
    {a₀ a₁ a₂ : (A : SSet.{u}) ⟶ X} (U : SSet.Homotopy a₀ a₁) (V : SSet.Homotopy a₁ a₂)
    {f₀ f₁ f₂ : K ⟶ Y} (G : SSet.Homotopy f₀ f₁) (H : SSet.Homotopy f₁ f₂)
    (hG : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = U.h ≫ k)
    (hH : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h = V.h ≫ k) :
    ∃ L : SSet.Homotopy a₀ a₂, ∃ T : SSet.Homotopy f₀ f₂,
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h = L.h ≫ k := by
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_quasiHomotopyTriangle U V
  have hb₀ : (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫ (F ≫ k) =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ G.h := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.homotopyTriangleComposite_first U V F hF]
    change (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫ (U.h ≫ k) =
      (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫
        ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h)
    rw [hG]
  have hb₁ : (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫ (F ≫ k) =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.homotopyTriangleComposite_last U V F hF]
    change (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫ (V.h ≫ k) =
      (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫
        ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h)
    rw [hH]
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyComposite A G H (F ≫ k) hb₀ hb₁
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.homotopyTriangleComposite U V F hF, T, hT⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
