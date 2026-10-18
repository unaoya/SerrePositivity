module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.Interface
public import SerrePositivity.InfinityCategories.Core.InitialCofinality
public import SerrePositivity.BhattScholze.PerfectoidizationInterface.InitialLimit
public import SerrePositivity.InfinityCategories.Derived.DiscreteCharacterization

/-! # 指定された普遍 perfectoid 化と導来極限の比較

概要：任意に与えた普遍単位を、同じ宇宙の標的圏の始対象として使う。
方針：環の一意因子分解を始対象性へ移し、二宇宙版の cofinality で指定錐を比較する。
規約：普遍環の存在は仮定せず、指定された単位の普遍性だけを引数に取る。
使われ方：Π2-5 の錐・単位付き導来同値、離散性、H⁰ の環同型。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime]

/-- 指定された普遍単位を、制限した標的圏の対象として保持する。 -/
def specifiedTarget (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) : PerfUnder_u p S :=
  ⟨Under.mk (CommRingCat.ofHom η), hC.1⟩

/-- 環の普遍性から得る、指定標的から任意の perfectoid 標的への射。 -/
def specifiedTargetTo (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) (T : PerfUnder_u p S) :
    specifiedTarget p S η hC ⟶ T :=
  ObjectProperty.homMk (Under.homMk
    (CommRingCat.ofHom (hC.2 T.obj.right T.property T.obj.hom.hom).choose)
    (CommRingCat.hom_ext (hC.2 T.obj.right T.property T.obj.hom.hom).choose_spec.1))

/-- 同じ Type u の全 perfectoid 標的に対する環の普遍性は、始対象性そのもの。 -/
def specifiedTarget_isInitial (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) : IsInitial (specifiedTarget p S η hC) := by
  letI (T : PerfUnder_u p S) : Unique (specifiedTarget p S η hC ⟶ T) :=
    { default := specifiedTargetTo p S η hC T
      uniq := fun f => by
        ext1
        ext1
        apply CommRingCat.hom_ext
        apply (hC.2 T.obj.right T.property T.obj.hom.hom).choose_spec.2
        exact congrArg (fun (g : S ⟶ T.obj.right) => g.hom) (Under.w f.hom) }
  exact IsInitial.ofUnique _

variable (R : Type u) [CommRing R]

/-- 指定された普遍環に、R → S を通した R 代数構造を与える。 -/
def specifiedAlgebra (S : A_R R) {C : Type u} [CommRing C]
    (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC) : A_R R :=
  (targetAlgebra R p S).obj (specifiedTarget p S.right ηC hC)

/-- 図式の一頂点への脚を、界面の join の一単体の表記で評価する。 -/
theorem coneLeg_edge {K X : SSet.{u + 1}} {G : K ⟶ X}
    (a : JoinCone G) (v : K _⦋0⦌) :
    (derivedConeLeg a v).edge = a.val.app _ (joinLegSimplex v) := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm v) ≫ a.val) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp]
  congr 1
  rw [SSet.yonedaEquiv_comp]
  have h00 : SSet.yonedaEquiv (joinStdSimplexIso 0 0 :
      join (Δ[0] : SSet.{u + 1}) Δ[0] ≅ Δ[1]).inv =
      joinLegSimplex (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1}))) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((joinStdSimplexIso 0 0).hom.app (Opposite.op ⦋1⦌))).injective
    rw [← SSet.yonedaEquiv_comp, Iso.inv_hom_id]
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  rw [h00]
  simp [joinLegSimplex, joinMap, Join.augHom]

section Interface
variable (hR : IsIntegralPerfectoid R p) (F : PerfectoidizationInterfaceE3 R p hR)
    (S : A_R R) {C : Type u} [CommRing C]
    (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC)

/-- 比較は指定された界面の錐と始対象からの標準錐の間の h(sliceOver) の同型。 -/
def specifiedLimitConeIso :
    (SSet.HomotopyCategory.mk (F.limitCone S).cone :
        SSet.hoFunctor.obj (sliceOver (targetDiagram R p S))) ≅
      SSet.HomotopyCategory.mk (initialValueCone
        (specifiedTarget_isInitial p S.right ηC hC) (targetDiagram R p S)) :=
  initialLimitConeIso (specifiedTarget_isInitial p S.right ηC hC)
    (targetDiagram R p S) (F.limitCone S).cone (F.limit_isLimit S)

/-- 指定錐の実際の射影は、指定普遍環への導来同値を表す。 -/
theorem specifiedProjection_isIso :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      ((F.limitCone S).projectionEdge (specifiedTarget p S.right ηC hC)).toTruncated) := by
  have := initialLimitLeg_isIso (specifiedTarget_isInitial p S.right ηC hC)
    (targetDiagram R p S) (F.limitCone S).cone (F.limit_isLimit S)
  apply coneEdge_isIso_of_edge_eq _ (derivedConeLeg (F.limitCone S).cone
    (nerveVertex (specifiedTarget p S.right ηC hC)))
  change ((F.limitCone S).projectionEdge (specifiedTarget p S.right ηC hC)).edge = _
  exact ((F.limitCone S).projectionEdge_eq _).trans (coneLeg_edge _ _).symm

/-- vertex perfd S と指定された C の離散像の同型。射は元の錐の射影である。 -/
def specifiedDerivedIso :
    (⟨vertex R F.perfd S⟩ : derivedInfinityHomotopyCategory R) ≅
      ⟨vertex R (J R) (specifiedAlgebra p R S ηC hC)⟩ := by
  have := specifiedProjection_isIso p R hR F S ηC hC
  exact asIso (SSet.Truncated.HomotopyCategory₂.homMk
    ((F.limitCone S).projectionEdge (specifiedTarget p S.right ηC hC)).toTruncated)

/-- 元の単位と比較同型の合成は、指定された S → C の離散像に一致する。 -/
theorem specifiedDerivedIso_unit :
    SSet.Truncated.HomotopyCategory₂.homMk (component R F.unit S).toTruncated ≫
        (specifiedDerivedIso p R hR F S ηC hC).hom =
      SSet.Truncated.HomotopyCategory₂.homMk
        (edge R (J R) (targetUnitMap R p S (specifiedTarget p S.right ηC hC))).toTruncated := by
  let T := specifiedTarget p S.right ηC hC
  let cc := F.limitCone S
  have hs : (derivedConeLeg (cc.sourceCone.postcomp (J R)) (nerveVertex T)).edge =
      (edge R (J R) (targetUnitMap R p S T)).edge := by
    rw [coneLeg_edge]
    change (J R).app _ (cc.sourceCone.val.app _ (joinLegSimplex (nerveVertex T))) = _
    rw [show nerveVertex T = ComposableArrows.mk₀ T from rfl, cc.source_legs T]
    rfl
  have hp : (derivedConeLeg cc.cone (nerveVertex T)).edge = (cc.projectionEdge T).edge := by
    rw [coneLeg_edge, cc.projectionEdge_eq]
    rfl
  let raw := derivedConeLegCompStruct cc.overSource.toTruncated (nerveVertex T)
  let triangle : SSet.Truncated.Edge.CompStruct (component R F.unit S).toTruncated
      (cc.projectionEdge T).toTruncated (edge R (J R) (targetUnitMap R p S T)).toTruncated :=
    ⟨raw.simplex, raw.d₂.trans cc.overSource_unit, raw.d₀.trans hp, raw.d₁.trans hs⟩
  exact triangle.homotopyCategory₂_fac

include ηC hC in
/-- 指定普遍環が存在すれば、導来 perfectoid 化全体は離散である。 -/
theorem specified_disc : Disc R (vertex R F.perfd S) := by
  have hJ : Disc R (vertex R (J R) (specifiedAlgebra p R S ηC hC)) :=
    moduleHeartVertex_disc ((discreteAlgebraModule R).obj (specifiedAlgebra p R S ηC hC))
  intro i hi
  exact (hJ i hi).of_iso ((HFunctor R i).mapIso (specifiedDerivedIso p R hR F S ηC hC))

/-- 指定錐の H⁰ 射影は、底の線形写像が同型なので環の同型である。 -/
theorem specifiedRingProjection_isIso :
    IsIso ((F.limitCone S).projection (specifiedTarget p S.right ηC hC)).right := by
  have := specifiedProjection_isIso p R hR F S ηC hC
  have hmap : IsIso ((discreteAlgebraModule R).map
      ((F.limitCone S).projection (specifiedTarget p S.right ηC hC))) := by
    rw [← (F.limitCone S).projection_compat]
    dsimp only [HMap]
    infer_instance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso ((discreteAlgebraModule R).map
    ((F.limitCone S).projection (specifiedTarget p S.right ηC hC)))

/-- H⁰ の環と指定普遍環の同型。射は指定錐の環準同型である。 -/
def specifiedRingIso : (F.h0.ringFunctor.obj S).right ≅ CommRingCat.of C := by
  have := specifiedRingProjection_isIso p R hR F S ηC hC
  exact asIso ((F.limitCone S).projection (specifiedTarget p S.right ηC hC)).right

/-- 環同型は元の二つの単位を保つ。 -/
theorem specifiedRingIso_unit :
    (specifiedRingIso p R hR F S ηC hC).hom.hom.comp (F.h0.unit.app S).right.hom = ηC :=
  congrArg (fun (f : S ⟶ specifiedAlgebra p R S ηC hC) => f.right.hom)
    ((F.limitCone S).projection_unit (specifiedTarget p S.right ηC hC))

end Interface

end SerrePositivity.BhattScholze.PerfectoidizationInterface
