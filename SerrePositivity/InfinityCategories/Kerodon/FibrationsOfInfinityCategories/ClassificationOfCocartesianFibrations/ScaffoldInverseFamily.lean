module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldMapping
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictDiagramScaffoldInverse
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianSectionFamilies

/-!
概要：水平辺を保つ scaffold の相対関手から、under 上の cocartesian section の族を得る。
方針：under の普遍評価を元の相対関手で写し、頂点を固定した辺が水平辺となることを使う。
規約：係数と相対関手の二つのパラメーターを全次数で保持する。
使われ方：cocartesian scaffold の写像空間比較の逆射。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- under の辺と固定した係数頂点を評価すると、輸送された頂点による水平辺となる。 -/
lemma simplicialReplacementUnderEvaluation_horizontal {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) (x : (F.obj c) _⦋0⦌)
    (e : (nerve (Under c)) _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c).app (Opposite.op ⦋1⦌)
      (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge F e.hom.right ((F.map (e.obj 0).hom).app _ x) := by
  obtain ⟨a, b, f, rfl⟩ := ComposableArrows.mk₁_surjective e
  change (⟨(ComposableArrows.mk₁ f) ⋙ Under.forget c,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) ≫ F.map a.hom⟩ :
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F 1) = _
  have hx : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) = SSet.const x := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hx, SSet.const_comp]
  refine Sigma.ext (ComposableArrows.ext₁ rfl rfl ?_) ?_
  · simp [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge]
  · apply heq_of_eq
    rfl

/-- under 評価と水平辺を保つ相対関手の、全パラメーターでの合成。 -/
def cocartesianScaffoldInverseFamily {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C) :
    nerve (Under c) ⊗ (F.obj c ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffoldFunctorSpace F q) ⟶ D :=
  (α_ (nerve (Under c)) (F.obj c) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffoldFunctorSpace F q)).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c ▷ _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFunctorInclusion F q)

/-- 全パラメーターの under 評価は同じ底の忘却射を被覆する。 -/
lemma cocartesianScaffoldInverseFamily_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C) :
    cocartesianScaffoldInverseFamily F q c ≫ q =
      fst (nerve (Under c)) (F.obj c ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffoldFunctorSpace F q) ≫
        nerveMap (Under.forget c) := by
  rw [cocartesianScaffoldInverseFamily, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c ▷ _), whiskerRight_fst,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation_projection]
  simp only [associator_inv_fst_fst_assoc]

/-- 二つのパラメーターの頂点を固定すると under 評価の全ての辺が cocartesian になる。 -/
lemma cocartesianScaffoldInverseFamily_horizontal {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C)
    (z : (F.obj c ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffoldFunctorSpace F q) _⦋0⦌)
    (e : (nerve (Under c)) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q ((cocartesianScaffoldInverseFamily F q c).app (Opposite.op ⦋1⦌)
      (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 1)) := by
  rcases z with ⟨x, v⟩
  obtain ⟨l, hl, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) v.val
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffoldFunctorPredicate F q v.val :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
  rw [← hv, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFunctorPredicate_vertex] at hc
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (v.val.val.app (Opposite.op ⦋1⦌)
    (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c).app (Opposite.op ⦋1⦌)
        (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)))
  rw [← hv]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (l.app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c).app _ (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)))
  rw [simplicialReplacementUnderEvaluation_horizontal]
  exact hc e.hom.right _

/-- 水平辺を保つ相対関手から、係数と相対関手をパラメーターとする section の族を得る。 -/
def cocartesianScaffoldInverseSectionFamily {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C) :
    F.obj c ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffoldFunctorSpace F q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport q c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsCurry (cocartesianScaffoldInverseFamily F q c)
    (cocartesianScaffoldInverseFamily_projection F q c)
    (cocartesianScaffoldInverseFamily_horizontal F q c)

/-- section の族を curry して、同じ相対関手を図式の逆比較の c 成分にする。 -/
def cocartesianScaffoldInverseComponent {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffoldFunctorSpace F q ⟶
      (ihom (F.obj c)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport q c) :=
  curry (cocartesianScaffoldInverseSectionFamily F q c)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
