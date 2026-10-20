module
public import SerrePositivity.InfinityCategories.Derived.PinchedHomComposition
public import SerrePositivity.InfinityCategories.Derived.PinchedHomChainMap

/-! # 実 pinched Hom の標準座標と任意鎖写像の成分

概要：標準 DK 座標を線形回収で表示し、任意 Hom 鎖写像の標準成分を計算する。
方針：符号変更と鎖写像の整数線形性を照合する。
規約：元の実単体を保つ。使われ方：AW 合成の閉前後合成との厳密比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded DGNerve.PinchedHom
open DoldKanComparison
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 実 pinched 単体は、その標準 DK 座標により一意に決まる。 -/
lemma pinchedHomStandard_injective (x y : D) (n : ℕ) :
    Function.Injective (fun f : (DGNerve.pinchedHom A D x y) _⦋n⦌ =>
      ((standardHomPinchedIso x y).inv.app _ f).down) := by
  intro f g h
  have hs : (standardHomPinchedIso x y).inv.app _ f =
      (standardHomPinchedIso x y).inv.app _ g := ULift.ext h
  have ht := congrArg ((standardHomPinchedIso x y).hom.app (Opposite.op ⦋n⦌)) hs
  simpa only [pinchedIso_inv_hom_apply] using ht
/-- 実 pinched 単体の標準 DK 座標を線形成分から直接読む。 -/
lemma pinchedHomStandard_coordinates {n : ℕ} (f : (DGNerve.pinchedHom A D x y) _⦋n⦌) :
    ((standardHomPinchedIso x y).inv.app _ f).down =
      standardSimplexEquiv x y n (toLinearSimplex f) := rfl
/-- Hom 鎖写像は標準 DK 座標の各成分に同じ鎖写像を適用する。 -/
lemma pinchedHomChainMap_standard_component {x' y' : D}
    (φ : homObject A D x y ⟶ homObject A D x' y')
    {n : ℕ} (f : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (((standardHomPinchedIso x' y').inv.app _ ((pinchedHomChainMap φ).app _ f)).down).val.component
      J k hJ hk =
    φ.f k ((((standardHomPinchedIso x y).inv.app _ f).down).val.component J k hJ hk) := by
  change (signChangeData (toLinearSimplex (pinchedHomChainMapSimplex φ f)).val).component
    J k hJ hk = φ.f k ((signChangeData (toLinearSimplex f).val).component J k hJ hk)
  rw [pinchedHomChainMapSimplex_linear, signChangeData_component, signChangeData_component]
  change degreeSign (J.card - 1) • φ.f k ((toLinearSimplex f).val.component J k hJ hk) =
    φ.f k (degreeSign (J.card - 1) • (toLinearSimplex f).val.component J k hJ hk)
  exact (map_zsmul _ _ _).symm

end SerrePositivity.InfinityCategories
