module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedChainMapComposition

/-! # Hom 鎖写像による線形単体写像の厳密な関手則

概要：線形単体への恒等写像と二回の写像を、元の鎖写像の恒等と合成に同定する。
方針：部分加群の台の全成分で照合する。
規約：全次元で厳密に成立。使われ方：相対ホモトピーの輸送端点の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D E T : Type v}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [_root_.SerrePositivity.DifferentialGraded.DGCategory A T]
variable {x y : D} {x' y' : E} {x'' y'' : T}

/-- 線形単体の二回の写像は、合成鎖写像の写像と厳密に一致。 -/
lemma pinchedLinearSimplexMap_comp
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y')
    (ψ : _root_.SerrePositivity.DifferentialGraded.homObject A E x' y' ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A T x'' y'') {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap ψ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (φ ≫ ψ) s := by
  apply Subtype.ext
  rfl

/-- 恒等鎖写像による線形単体の像は元の単体。 -/
lemma pinchedLinearSimplexMap_id {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (𝟙 (homObject A D x y)) s = s := by
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
