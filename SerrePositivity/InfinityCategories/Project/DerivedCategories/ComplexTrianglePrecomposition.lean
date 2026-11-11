module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SourceTriangleComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexTrianglePostcomposition

/-! # 複体の合成三角形への始点の前合成

概要：始点を鎖写像で置き換えた dg nerve 三角形を、二辺とホモトピーの前合成として計算する。
方針：閉零射との合成の微分式と低次単体の外延性を使う。
規約：始点からの合成の順序を保つ。使われ方：D7 の suspension 比較の中央四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {V W X Y : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 始点の前合成は三角形の微分方程式を保つ。 -/
lemma complexTriangle_precompose_differential (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (p : V ⟶ W) :
    δ (-1) 0 ((Cochain.ofHom p).comp t (zero_add (-1))) =
      Cochain.ofHom ((p ≫ a) ≫ b) - Cochain.ofHom (p ≫ c) := by
  rw [δ_ofHom_comp, ht, Cochain.comp_sub, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    Category.assoc]

/-- 二辺とホモトピーに始点の鎖写像を前合成した三角形。 -/
def precomposeComplexTriangle (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (p : V ⟶ W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 2 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct (p ≫ a) b (p ≫ c) ((Cochain.ofHom p).comp t (zero_add (-1)))
    (complexTriangle_precompose_differential a b c t ht p)).simplex

/-- 一般の始点の前合成単体は複体の明示的前合成三角形に一致する。 -/
lemma sourcePrecomposition_complexTriangle (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (p : V ⟶ W) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a b c t ht).simplex
      ⟨Cochain.ofHom p, δ_ofHom p⟩ = precomposeComplexTriangle a b c t ht p := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i; fin_cases i <;> rfl
  · apply heq_of_eq
    calc
      _ = _root_.SerrePositivity.DifferentialGraded.compose (D := _root_.SerrePositivity.DifferentialGraded.Complex S) S (Cochain.ofHom a) (Cochain.ofHom p) (zero_add 0) :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge01 _ _
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, ← Cochain.ofHom_comp]; rfl
  · rfl
  · apply heq_of_eq
    calc
      _ = _root_.SerrePositivity.DifferentialGraded.compose (D := _root_.SerrePositivity.DifferentialGraded.Complex S) S (Cochain.ofHom c) (Cochain.ofHom p) (zero_add 0) :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge02 _ _
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, ← Cochain.ofHom_comp]; rfl
  · apply heq_of_eq
    calc
      _ = _root_.SerrePositivity.DifferentialGraded.compose (D := _root_.SerrePositivity.DifferentialGraded.Complex S) S t (Cochain.ofHom p) (zero_add (-1)) :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_triple _ _
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
