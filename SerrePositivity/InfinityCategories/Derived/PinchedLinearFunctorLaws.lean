module
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapComposition

/-! # Hom 鎖写像による線形単体写像の厳密な関手則

概要：線形単体への恒等写像と二回の写像を、元の鎖写像の恒等と合成に同定する。
方針：部分加群の台の全成分で照合する。
規約：全次元で厳密に成立。使われ方：相対ホモトピーの輸送端点の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
variable {A : Type u} [CommRing A] {D E T : Type v}
variable [DGCategory A D] [DGCategory A E] [DGCategory A T]
variable {x y : D} {x' y' : E} {x'' y'' : T}

/-- 線形単体の二回の写像は、合成鎖写像の写像と厳密に一致。 -/
lemma pinchedLinearSimplexMap_comp
    (φ : homObject A D x y ⟶ homObject A E x' y')
    (ψ : homObject A E x' y' ⟶ homObject A T x'' y'') {n : ℕ}
    (s : LinearSimplex A x y n) :
    pinchedLinearSimplexMap ψ (pinchedLinearSimplexMap φ s) =
      pinchedLinearSimplexMap (φ ≫ ψ) s := by
  apply Subtype.ext
  rfl

/-- 恒等鎖写像による線形単体の像は元の単体。 -/
lemma pinchedLinearSimplexMap_id {n : ℕ} (s : LinearSimplex A x y n) :
    pinchedLinearSimplexMap (𝟙 (homObject A D x y)) s = s := by
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories
