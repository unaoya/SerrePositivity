module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedEndpointConeSpace

/-!
概要：両端固定の関手空間と、図式と頂点の二重 fiber としての錐の空間の同型。
方針：両端の固定条件を個別に回収して二回持ち上げ、包含後の値で往復を計算する。
規約：充填性を仮定しない厳密な同型。
使われ方：Kerodon 4.6.6.8、7.4.1.6、7.5.4.6 の固定条件を保つ比較の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：両端固定の錐の右端は元の図式に定値。
方針：両端の fiber の条件を右端へ制限する。
規約：全次数での固定条件。
使われ方：Kerodon 4.6.6.8 の図式の fiber への持ち上げ。 -/
lemma fixedEndpointConeSpace_inr {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    vertexFiberι ((pre (joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
      (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) p)) ≫
      (pre (joinInr Δ[0] K)).app X = SSet.const (functorVertex p) := by
  have h := fixedDiagramι_pre_factor (joinEndpointInclusion (Δ[0] : SSet.{u}) K)
    (joinEndpointDesc (SSet.yonedaEquiv.symm x) p) (joinEndpointInr Δ[0] K)
  rw [joinEndpointInr_inclusion] at h
  exact h

/-- 概要：両端固定の錐の左端は指定頂点の一点の図式に定値。
方針：両端の fiber の条件を左端へ制限する。
規約：X の充填性を要求しない。
使われ方：Kerodon 4.6.6.8 の頂点の fiber への持ち上げ。 -/
lemma fixedEndpointConeSpace_inl {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    vertexFiberι ((pre (joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
      (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) p)) ≫
      (pre (joinInl (Δ[0] : SSet.{u}) K)).app X =
        SSet.const (functorVertex (SSet.yonedaEquiv.symm x)) := by
  have h := fixedDiagramι_pre_factor (joinEndpointInclusion (Δ[0] : SSet.{u}) K)
    (joinEndpointDesc (SSet.yonedaEquiv.symm x) p) (joinEndpointInl Δ[0] K)
  rw [joinEndpointInl_inclusion] at h
  exact h

/-- 概要：両端固定の錐を図式だけを固定した錐へ移す。
方針：右端の固定条件で関手空間の包含を持ち上げる。
規約：元の関手の族の値を保存する。
使われ方：Kerodon 4.6.6.8 の二重 fiber への逆射の第一段階。 -/
def endpointConeSpaceToFamily {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedEndpointConeSpace p x ⟶ coneFamily p :=
  vertexFiberLift (coneRestriction K X) (functorVertex p)
    (vertexFiberι ((pre (joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
      (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) p)))
    (fixedEndpointConeSpace_inr p x)

/-- 概要：両端固定の錐の頂点は指定頂点に定値。
方針：左端の固定条件を一点の関手空間で評価する。
規約：頂点の固定は射の等式である。
使われ方：Kerodon 4.6.6.8 の二重 fiber への逆射の第二段階。 -/
lemma endpointConeSpaceToFamily_apex {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    endpointConeSpaceToFamily p x ≫ coneFamilyApex p = SSet.const x := by
  change (endpointConeSpaceToFamily p x ≫
    vertexFiberι (coneRestriction K X) (functorVertex p)) ≫
    (pre (joinInl (Δ[0] : SSet.{u}) K)).app X ≫
    (pointFunctorEvaluationIso X).hom = _
  rw [endpointConeSpaceToFamily, vertexFiberLift_ι, ← Category.assoc,
    fixedEndpointConeSpace_inl, SSet.const_comp]
  congr 1
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

/-- 概要：両端固定の単一 fiber を図式と頂点の二重 fiber へ移す。
方針：図式の fiber への射を頂点の固定条件でもう一度持ち上げる。
規約：射の定義に quasicategory 性は不要。
使われ方：Kerodon 4.6.6.8 の二つの表示の逆射。 -/
def endpointConeSpaceToFixedApex {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedEndpointConeSpace p x ⟶ fixedApexConeFamily p x :=
  vertexFiberLift (coneFamilyApex p) x (endpointConeSpaceToFamily p x)
    (endpointConeSpaceToFamily_apex p x)

/-- 概要：固定頂点の錐の二重 fiber は両端固定の関手空間の fiber と同型。
方針：二つの持ち上げの往復は関手の値を変えないことを各次数で確認する。
規約：X と K は任意で、同値より強い厳密な同型を与える。
使われ方：Kerodon 4.6.6.8、7.4.1.6 の両端固定の fat join 比較の移送。 -/
def fixedApexEndpointConeSpaceIso {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    fixedApexConeFamily p x ≅ fixedEndpointConeSpace p x where
  hom := fixedApexToEndpointConeSpace p x
  inv := endpointConeSpaceToFixedApex p x
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
