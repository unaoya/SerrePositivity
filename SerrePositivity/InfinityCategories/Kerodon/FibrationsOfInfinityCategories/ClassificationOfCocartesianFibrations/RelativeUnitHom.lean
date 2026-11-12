module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeComposition

/-!
概要：元の cocartesian 辺を保つ底上の射と、制限した豊穣 Hom の単位からの射との対応。
方針：元の相対 Hom の零単体の同値を辺の保存条件で制限する。
規約：通常の射の恒等・合成と、同じ豊穣単位・合成の対応も厳密に証明する。
使われ方：cocartesian fibrations の core 移送前の単体的圏。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 全部分複体の頂点は、指定した条件を満たす元の頂点と全単射。 -/
def fullSubcomplexVertexEquiv {X : SSet.{u}} (P : X _⦋0⦌ → Prop) :
    {v : X _⦋0⦌ // P v} ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌ where
  toFun v := ⟨v.val, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, X.map_id_apply]
    exact v.property⟩
  invFun v := ⟨v.val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 辺を保つ底上の実際の射と、その相対関手の全部分複体の頂点は全単射。 -/
def cocartesianRelativeFunctorVertexEquiv {B : SSet.{u}} (a b : Over B) :
    {f : a ⟶ b // _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges a.hom b.hom f.left} ≃
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace a.hom b.hom) _⦋0⦌ :=
  (Equiv.subtypeEquiv
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.overHomEquivSubtype a b).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv b.hom a.hom)) (by
      intro f
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorPredicate_vertex a.hom b.hom f.left f.w).symm)).trans
    (fullSubcomplexVertexEquiv _)

/-- 通常の cocartesian な底上の射と、相対豊穣 Hom の単位からの射は全単射。 -/
def cocartesianRelativeFunctorHomEquiv {B : SSet.{u}} (a b : Over B) :
    {f : a ⟶ b // _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges a.hom b.hom f.left} ≃
      (𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace a.hom b.hom) :=
  (cocartesianRelativeFunctorVertexEquiv a b).trans (SSet.unitHomEquiv _).symm

/-- 通常の恒等射は、同じ相対豊穣単位と対応する。 -/
lemma cocartesianRelativeFunctorHomEquiv_id {B : SSet.{u}} (a : Over B) :
    cocartesianRelativeFunctorHomEquiv a a ⟨𝟙 a, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.preservesCocartesianEdges_id a.hom⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorIdentity a := by
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  exact congrArg (SSet.unitHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace a.hom a.hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_id a)

/-- 通常の二射の合成は、同じ相対豊穣合成と対応する。 -/
lemma cocartesianRelativeFunctorHomEquiv_comp {B : SSet.{u}} {a b c : Over B}
    (f : {f : a ⟶ b // _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges a.hom b.hom f.left})
    (g : {g : b ⟶ c // _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges b.hom c.hom g.left}) :
    cocartesianRelativeFunctorHomEquiv a c ⟨f.val ≫ g.val, f.property.comp g.property⟩ =
      (λ_ (𝟙_ SSet.{u})).inv ≫
        (cocartesianRelativeFunctorHomEquiv a b f ⊗ₘ cocartesianRelativeFunctorHomEquiv b c g) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorComposition a b c := by
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  exact congrArg (SSet.unitHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom a.hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_comp f.val g.val)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
