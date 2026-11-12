module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FirstFixedCompositionExt
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceFaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceDiagonal
/-!
概要：任意の元入力を持つ合成対応の射を、実三角形と元入力で同定する。
方針：入力の引き戻しの外延性と三角形評価の単射性を使う。
規約：対角だけの一致に弱めない。使われ方：元終域の補正道の端点比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {Z A T : SSet.{u}} {x y z : Z _⦋0⦌}

lemma dgGluingTriangleEvaluation_precomp {P Q V W : SSet.{u}}
    (i : P ⟶ Q) (a : Q ⟶ V) (ev : (Δ[2] : SSet.{u}) ⊗ V ⟶ W)
    {tri : (Δ[2] : SSet.{u}) ⊗ Q ⟶ W} (h : (Δ[2] ◁ a) ≫ ev = tri) :
    (Δ[2] ◁ (i ≫ a)) ≫ ev = (Δ[2] ◁ i) ≫ tri := by
  rw [whiskerLeft_comp, Category.assoc, h]

def dgGluingFirstRestrictedTriangleEvaluation (f : Z.Edge x y) (z : Z _⦋0⦌)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y z) :=
  (Δ[2] ◁ pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z) a) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z

def dgGluingLastRestrictedTriangleEvaluation (x : Z _⦋0⦌) (g : Z.Edge y z)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :=
  (Δ[2] ◁ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x g) a) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x g

lemma dgGluingFirstRestrictedTriangleEvaluation_diagonal (f : Z.Edge x y) (z : Z _⦋0⦌)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y z) :
    (stdSimplex.δ (1 : Fin 3) ▷ pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z) a) ≫
      dgGluingFirstRestrictedTriangleEvaluation f z a =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z) a ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionDiagonal f z) := by
  rw [dgGluingFirstRestrictedTriangleEvaluation, ← Category.assoc, ← whisker_exchange,
    Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionDiagonal_uncurry,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

lemma dgGluingLastRestrictedTriangleEvaluation_diagonal (x : Z _⦋0⦌) (g : Z.Edge y z)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    (stdSimplex.δ (1 : Fin 3) ▷ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x g) a) ≫
      dgGluingLastRestrictedTriangleEvaluation x g a =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x g) a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g) := by
  rw [dgGluingLastRestrictedTriangleEvaluation, ← Category.assoc, ← whisker_exchange,
    Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal_uncurry,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

lemma dgGluingFirstRestrictedTriangle_hom_ext (f : Z.Edge x y) (z : Z _⦋0⦌)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y z)
    {l r : T ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z) a}
    (ht : (Δ[2] ◁ l) ≫ dgGluingFirstRestrictedTriangleEvaluation f z a =
      (Δ[2] ◁ r) ≫ dgGluingFirstRestrictedTriangleEvaluation f z a)
    (hp : l ≫ pullback.snd _ _ = r ≫ pullback.snd _ _) : l = r := by
  apply pullback.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedComposition_hom_ext_triangle
    apply uncurry_injective
    simpa only [uncurry_natural_left, whiskerLeft_comp, Category.assoc,
      dgGluingFirstRestrictedTriangleEvaluation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation] using ht
  · exact hp

lemma dgGluingLastRestrictedTriangle_hom_ext (x : Z _⦋0⦌) (g : Z.Edge y z)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)
    {l r : T ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x g) a}
    (ht : (Δ[2] ◁ l) ≫ dgGluingLastRestrictedTriangleEvaluation x g a =
      (Δ[2] ◁ r) ≫ dgGluingLastRestrictedTriangleEvaluation x g a)
    (hp : l ≫ pullback.snd _ _ = r ≫ pullback.snd _ _) : l = r := by
  apply pullback.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence_hom_ext_triangle
    apply uncurry_injective
    simpa only [uncurry_natural_left, whiskerLeft_comp, Category.assoc,
      dgGluingLastRestrictedTriangleEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation] using ht
  · exact hp

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
