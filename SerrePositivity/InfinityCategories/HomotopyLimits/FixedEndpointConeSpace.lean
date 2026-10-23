module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeFamilyApex
public import SerrePositivity.InfinityCategories.F1.Joins.JoinEndpointMaps
public import SerrePositivity.InfinityCategories.F1.Diagrams.FixedDiagramRestriction

/-!
概要：固定頂点の内部 Hom の錐を、join の両端固定の関手空間で表示する。
方針：両端の直和からの制限を二つの制限に分け、二重 fiber と一つの fiber を往復する。
規約：全次数での厳密な同型であり、quasicategory 性は要求しない。
使われ方：Kerodon 4.6.6.8、7.4.1.6、7.5.4.6 の固定頂点を保つ模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：両端の直和上の関手の族は、左右の制限で決まる。
方針：uncurry して直和の二つの場合で射の等式を検査する。
規約：全ての単体集合とパラメータについて成り立つ。
使われ方：Kerodon §4.6.6、両端を同時に固定した fiber の普遍性。 -/
lemma joinEndpointFunctor_hom_ext {A B T X : SSet.{u}}
    {f g : T ⟶ (ihom (joinEndpointDiagram A B)).obj X}
    (hl : f ≫ (pre (joinEndpointInl A B)).app X =
      g ≫ (pre (joinEndpointInl A B)).app X)
    (hr : f ≫ (pre (joinEndpointInr A B)).app X =
      g ≫ (pre (joinEndpointInr A B)).app X) : f = g := by
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
使われ方：Kerodon 4.6.6.8、7.4.1.6 の両端固定の fat join 比較の始域。 -/
def fixedEndpointConeSpace {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) : SSet.{u} :=
  vertexFiber ((pre (joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) p))

/-- 概要：固定頂点の二重 fiber から錐の関手空間への包含。
方針：頂点の fiber と図式の fiber の包含を合成する。
規約：比較射の両方向で同じ包含を使う。
使われ方：Kerodon 4.6.6.8 の二重 fiber と両端固定の fiber の同定。 -/
def fixedApexConeFamilyEvaluation {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedApexConeFamily p x ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X :=
  vertexFiberι (coneFamilyApex p) x ≫
    vertexFiberι (coneRestriction K X) (functorVertex p)

/-- 概要：固定頂点の二重 fiber の右端は元の図式に定値。
方針：図式の fiber の包含の固定条件を使う。
規約：射の厳密な等式。
使われ方：Kerodon 4.6.6.8 の両端固定の fiber への持ち上げ。 -/
lemma fixedApexConeFamilyEvaluation_inr {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedApexConeFamilyEvaluation p x ≫ (pre (joinInr Δ[0] K)).app X =
      SSet.const (functorVertex p) := by
  change vertexFiberι (coneFamilyApex p) x ≫
    (vertexFiberι (coneRestriction K X) (functorVertex p) ≫ coneRestriction K X) = _
  rw [vertexFiberι_comp, SSet.comp_const]

/-- 概要：固定頂点の二重 fiber の左端は指定頂点の一点の図式に定値。
方針：一点の関手空間の評価同型で消去して、頂点 fiber の条件を使う。
規約：X の充填性は使わない。
使われ方：Kerodon 4.6.6.8 の両端固定の fiber への持ち上げ。 -/
lemma fixedApexConeFamilyEvaluation_inl {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedApexConeFamilyEvaluation p x ≫ (pre (joinInl (Δ[0] : SSet.{u}) K)).app X =
      SSet.const (functorVertex (SSet.yonedaEquiv.symm x)) := by
  apply (cancel_mono (pointFunctorEvaluationIso X).hom).mp
  rw [SSet.const_comp]
  change vertexFiberι (coneFamilyApex p) x ≫ coneFamilyApex p = _
  rw [vertexFiberι_comp]
  congr 1
  symm
  change (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)).app (Opposite.op ⦋0⦌)
    (functorVertex (SSet.yonedaEquiv.symm x)) = x
  rw [evaluateFunctorAt_functorVertex, SSet.yonedaEquiv_symm_app]
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
使われ方：Kerodon 4.6.6.8、7.4.1.6 の一つの fiber への射。 -/
lemma fixedApexConeFamilyEvaluation_fixed {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedApexConeFamilyEvaluation p x ≫
      (pre (joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X =
      SSet.const (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) p)) := by
  apply joinEndpointFunctor_hom_ext
  · rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, joinEndpointInl_inclusion,
      fixedApexConeFamilyEvaluation_inl, SSet.const_comp]
    rfl
  · rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, joinEndpointInr_inclusion,
      fixedApexConeFamilyEvaluation_inr, SSet.const_comp]
    rfl

/-- 概要：二重 fiber の固定頂点の錐を両端固定の単一 fiber へ移す。
方針：共通の関手空間への包含を両端固定条件で持ち上げる。
規約：射の定義は全次数で関手の族を保存する。
使われ方：Kerodon 4.6.6.8 の二つの固定条件の表示の比較。 -/
def fixedApexToEndpointConeSpace {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedApexConeFamily p x ⟶ fixedEndpointConeSpace p x :=
  vertexFiberLift _ _ (fixedApexConeFamilyEvaluation p x)
    (fixedApexConeFamilyEvaluation_fixed p x)

end SerrePositivity.InfinityCategories.HomotopyLimits
