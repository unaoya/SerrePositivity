module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamilyApex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedDiagramRestriction

/-!
概要：固定頂点の内部 Hom の錐を、join の両端固定の関手空間で表示する。
方針：両端の直和からの制限を二つの制限に分け、二重 fiber と一つの fiber を往復する。
規約：全次数での厳密な同型であり、quasicategory 性は要求しない。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の固定頂点を保つ模型の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：両端の直和上の関手の族は、左右の制限で決まる。
方針：uncurry して直和の二つの場合で射の等式を検査する。
規約：全ての単体集合とパラメータについて成り立つ。
使われ方：Kerodon §4.6.6（Tag 04HY）、両端を同時に固定した fiber の普遍性。 -/
lemma joinEndpointFunctor_hom_ext {A B T X : SSet.{u}}
    {f g : T ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram A B)).obj X}
    (hl : f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl A B)).app X =
      g ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl A B)).app X)
    (hr : f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr A B)).app X =
      g ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr A B)).app X) : f = g := by
  apply uncurry_injective
  have hl' := congrArg (fun h : T ⟶ (ihom A).obj X ↦ uncurry h) hl
  have hr' := congrArg (fun h : T ⟶ (ihom B).obj X ↦ uncurry h) hr
  rw [uncurry_pre_app, uncurry_pre_app] at hl' hr'
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  cases s with
  | inl a => exact congrArg (fun h : A ⊗ T ⟶ X ↦ h.app d (a, t)) hl'
  | inr b => exact congrArg (fun h : B ⊗ T ⟶ X ↦ h.app d (b, t)) hr'

/-- 概要：頂点と図式を一つの両端固定条件として指定する錐の関手空間。
方針：左右の因子の直和からの制限の、指定図式上の fiber を取る。
規約：左端は x の一点、右端は p。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS） の両端固定の fat join 比較の始域。 -/
def fixedEndpointConeSpace {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))

/-- 概要：固定頂点の二重 fiber から錐の関手空間への包含。
方針：頂点の fiber と図式の fiber の包含を合成する。
規約：比較射の両方向で同じ包含を使う。
使われ方：Kerodon 4.6.6.8（Tag 04J5） の二重 fiber と両端固定の fiber の同定。 -/
def fixedApexConeFamilyEvaluation {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).obj X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p) x ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- 概要：固定頂点の二重 fiber の右端は元の図式に定値。
方針：図式の fiber の包含の固定条件を使う。
規約：射の厳密な等式。
使われ方：Kerodon 4.6.6.8（Tag 04J5） の両端固定の fiber への持ち上げ。 -/
lemma fixedApexConeFamilyEvaluation_inr {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedApexConeFamilyEvaluation p x ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p) x ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

/-- 概要：固定頂点の二重 fiber の左端は指定頂点の一点の図式に定値。
方針：一点の関手空間の評価同型で消去して、頂点 fiber の条件を使う。
規約：X の充填性は使わない。
使われ方：Kerodon 4.6.6.8（Tag 04J5） の両端固定の fiber への持ち上げ。 -/
lemma fixedApexConeFamilyEvaluation_inl {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedApexConeFamilyEvaluation p x ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K)).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x)) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom).mp
  rw [SSet.const_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p) x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
  congr 1
  symm
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x)) = x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, SSet.yonedaEquiv_symm_app]
  have hi : stdSimplex.objEquiv (stdSimplex.obj₀Equiv.symm 0) = 𝟙 ⦋0⦌ := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    change (_ : Fin 1) = _
    omega
  rw [hi]
  exact CategoryTheory.Functor.map_id_apply X _ x

/-- 概要：固定頂点の二重 fiber の錐は両端の直和上で指定図式に定値。
方針：両端の関手の族の一意性を使い、左右の固定条件を合わせる。
規約：両端の整合性に高次の追加仮定は不要。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS） の一つの fiber への射。 -/
lemma fixedApexConeFamilyEvaluation_fixed {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedApexConeFamilyEvaluation p x ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p)) := by
  apply joinEndpointFunctor_hom_ext
  · rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_inclusion,
      fixedApexConeFamilyEvaluation_inl, SSet.const_comp]
    rfl
  · rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_inclusion,
      fixedApexConeFamilyEvaluation_inr, SSet.const_comp]
    rfl

/-- 概要：二重 fiber の固定頂点の錐を両端固定の単一 fiber へ移す。
方針：共通の関手空間への包含を両端固定条件で持ち上げる。
規約：射の定義は全次数で関手の族を保存する。
使われ方：Kerodon 4.6.6.8（Tag 04J5） の二つの固定条件の表示の比較。 -/
def fixedApexToEndpointConeSpace {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x ⟶ fixedEndpointConeSpace p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (fixedApexConeFamilyEvaluation p x)
    (fixedApexConeFamilyEvaluation_fixed p x)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
