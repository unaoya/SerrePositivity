module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldMapping
public import SerrePositivity.InfinityCategories.F1.StrictDiagramScaffoldInverse
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianSectionFamilies

/-!
概要：水平辺を保つ scaffold の相対関手から、under 上の cocartesian section の族を得る。
方針：under の普遍評価を元の相対関手で写し、頂点を固定した辺が水平辺となることを使う。
規約：係数と相対関手の二つのパラメーターを全次数で保持する。
使われ方：cocartesian scaffold の写像空間比較の逆射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- under の辺と固定した係数頂点を評価すると、輸送された頂点による水平辺となる。 -/
lemma simplicialReplacementUnderEvaluation_horizontal {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) (x : (F.obj c) _⦋0⦌)
    (e : (nerve (Under c)) _⦋1⦌) :
    (simplicialReplacementUnderEvaluation F c).app (Opposite.op ⦋1⦌)
      (e, PinchedHom.constant x 1) =
      kanScaffoldHorizontalEdge F e.hom.right ((F.map (e.obj 0).hom).app _ x) := by
  obtain ⟨a, b, f, rfl⟩ := ComposableArrows.mk₁_surjective e
  change (⟨(ComposableArrows.mk₁ f) ⋙ Under.forget c,
    SSet.yonedaEquiv.symm (PinchedHom.constant x 1) ≫ F.map a.hom⟩ :
      simplicialReplacementSimplex F 1) = _
  have hx : SSet.yonedaEquiv.symm (PinchedHom.constant x 1) = SSet.const x := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hx, SSet.const_comp]
  refine Sigma.ext (ComposableArrows.ext₁ rfl rfl ?_) ?_
  · simp [kanScaffoldHorizontalEdge]
  · apply heq_of_eq
    rfl

/-- under 評価と水平辺を保つ相対関手の、全パラメーターでの合成。 -/
def cocartesianScaffoldInverseFamily {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C) :
    nerve (Under c) ⊗ (F.obj c ⊗ CocartesianScaffoldFunctorSpace F q) ⟶ D :=
  (α_ (nerve (Under c)) (F.obj c) (CocartesianScaffoldFunctorSpace F q)).inv ≫
    (simplicialReplacementUnderEvaluation F c ▷ _) ≫
      relativeFunctorUncurry (cocartesianScaffoldFunctorInclusion F q)

/-- 全パラメーターの under 評価は同じ底の忘却射を被覆する。 -/
lemma cocartesianScaffoldInverseFamily_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C) :
    cocartesianScaffoldInverseFamily F q c ≫ q =
      fst (nerve (Under c)) (F.obj c ⊗ CocartesianScaffoldFunctorSpace F q) ≫
        nerveMap (Under.forget c) := by
  rw [cocartesianScaffoldInverseFamily, Category.assoc, Category.assoc,
    relativeFunctorUncurry_projection,
    ← Category.assoc (simplicialReplacementUnderEvaluation F c ▷ _), whiskerRight_fst,
    Category.assoc, simplicialReplacementUnderEvaluation_projection]
  simp only [associator_inv_fst_fst_assoc]

/-- 二つのパラメーターの頂点を固定すると under 評価の全ての辺が cocartesian になる。 -/
lemma cocartesianScaffoldInverseFamily_horizontal {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C)
    (z : (F.obj c ⊗ CocartesianScaffoldFunctorSpace F q) _⦋0⦌)
    (e : (nerve (Under c)) _⦋1⦌) :
    IsCocartesianEdge q ((cocartesianScaffoldInverseFamily F q c).app (Opposite.op ⦋1⦌)
      (e, PinchedHom.constant z 1)) := by
  rcases z with ⟨x, v⟩
  obtain ⟨l, hl, hv⟩ := exists_relativeFunctorVertex q (simplicialReplacementProjection F) v.val
  have hc : CocartesianScaffoldFunctorPredicate F q v.val :=
    fullSubcomplexOnVertices_vertex v
  rw [← hv, cocartesianScaffoldFunctorPredicate_vertex] at hc
  change IsCocartesianEdge q (v.val.val.app (Opposite.op ⦋1⦌)
    (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op
      ((simplicialReplacementUnderEvaluation F c).app (Opposite.op ⦋1⦌)
        (e, PinchedHom.constant x 1)))
  rw [← hv]
  change IsCocartesianEdge q (l.app _
    ((simplicialReplacementUnderEvaluation F c).app _ (e, PinchedHom.constant x 1)))
  rw [simplicialReplacementUnderEvaluation_horizontal]
  exact hc e.hom.right _

/-- 水平辺を保つ相対関手から、係数と相対関手をパラメーターとする section の族を得る。 -/
def cocartesianScaffoldInverseSectionFamily {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C) :
    F.obj c ⊗ CocartesianScaffoldFunctorSpace F q ⟶ kanCocartesianStrictTransport q c :=
  kanCocartesianSectionsCurry (cocartesianScaffoldInverseFamily F q c)
    (cocartesianScaffoldInverseFamily_projection F q c)
    (cocartesianScaffoldInverseFamily_horizontal F q c)

/-- section の族を curry して、同じ相対関手を図式の逆比較の c 成分にする。 -/
def cocartesianScaffoldInverseComponent {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C) :
    CocartesianScaffoldFunctorSpace F q ⟶
      (ihom (F.obj c)).obj (kanCocartesianStrictTransport q c) :=
  curry (cocartesianScaffoldInverseSectionFamily F q c)

end SerrePositivity.InfinityCategories
