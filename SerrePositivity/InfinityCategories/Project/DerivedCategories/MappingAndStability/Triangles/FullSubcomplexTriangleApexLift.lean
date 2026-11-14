module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.FullSubcomplexTriangleLift

/-! # 始頂点の所属と指定零面からの実三角形の全部分複体への持ち上げ

概要：零面が指定部分複体に入り、残る始頂点も入れば、同じ実二単体全体を持ち上げる。
方針：三頂点を標準頂点射へ分解し、始頂点条件と零面の二頂点条件を使う。
規約：元の二単体と零面を厳密に保つ。使われ方：実 over 三角形を実分母 over へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (P : X _⦋0⦌ → Prop)

/-- 始頂点の所属と指定零面から、元の実二単体を全部分複体へ持ち上げる。 -/
def fullSubcomplexTriangleApexLift (T : X _⦋2⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋1⦌)
    (h₀ : X.δ 0 T = e.val) (hA : P (X.δ 1 (X.δ 1 T))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋2⦌ := by
  refine ⟨T, ?_⟩
  intro v
  generalize hi : v.toOrderHom 0 = i
  fin_cases i
  · have he : v = SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3) :=
      SimplexCategory.Hom.ext_zero_left _ _ hi
    rw [he, op_comp, Functor.map_comp_apply]
    exact hA
  · have he : v = SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) :=
      SimplexCategory.Hom.ext_zero_left _ _ hi
    rw [he, op_comp, Functor.map_comp_apply]
    change P (X.δ 1 (X.δ 0 T))
    rw [h₀]
    exact e.property (SimplexCategory.δ (1 : Fin 2))
  · have he : v = SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) :=
      SimplexCategory.Hom.ext_zero_left _ _ hi
    rw [he, op_comp, Functor.map_comp_apply]
    change P (X.δ 0 (X.δ 0 T))
    rw [h₀]
    exact e.property (SimplexCategory.δ (0 : Fin 2))

/-- 始頂点条件から持ち上げた実三角形の台は元の二単体そのもの。 -/
lemma fullSubcomplexTriangleApexLift_val (T : X _⦋2⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋1⦌)
    (h₀ : X.δ 0 T = e.val) (hA : P (X.δ 1 (X.δ 1 T))) :
    (fullSubcomplexTriangleApexLift P T e h₀ hA).val = T := rfl

/-- 始頂点条件から持ち上げた実三角形の零面は、元の指定部分複体辺と厳密に一致。 -/
lemma fullSubcomplexTriangleApexLift_face0 (T : X _⦋2⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋1⦌)
    (h₀ : X.δ 0 T = e.val) (hA : P (X.δ 1 (X.δ 1 T))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}).δ 0
      (fullSubcomplexTriangleApexLift P T e h₀ hA) = e := Subtype.ext h₀

end SerrePositivity.InfinityCategories.Project.DerivedCategories
