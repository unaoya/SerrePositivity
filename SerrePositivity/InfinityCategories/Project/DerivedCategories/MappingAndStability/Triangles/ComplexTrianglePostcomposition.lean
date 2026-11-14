module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.TriangleExt
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexTriangleComponents

/-! # 複体の合成三角形への後合成

概要：三角形の終域への鎖写像を二辺とホモトピーへ後合成する。
方針：閉零 cochain との合成は微分と可換であることを使う。
規約：元の始域と中間対象を保つ。使われ方：D7 の双対比較三単体の終点面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {W X Y Z : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 合成三角形の微分方程式は終域への後合成で保たれる。 -/
lemma complexTriangle_postcompose_differential (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    δ (-1) 0 (t.comp (Cochain.ofHom q) (add_zero (-1))) =
      Cochain.ofHom (a ≫ (b ≫ q)) - Cochain.ofHom (c ≫ q) := by
  rw [δ_comp_ofHom, ht, Cochain.sub_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    Category.assoc]

/-- 二辺とホモトピーを終域への鎖写像で後合成した二単体。 -/
def postcomposeComplexTriangle (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 2 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a (b ≫ q) (c ≫ q) (t.comp (Cochain.ofHom q) (add_zero (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangle_postcompose_differential a b c t ht q)).simplex

end SerrePositivity.InfinityCategories.Project.DerivedCategories
