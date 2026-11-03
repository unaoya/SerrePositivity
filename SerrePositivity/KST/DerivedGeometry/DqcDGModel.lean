module

public import SerrePositivity.KST.DerivedGeometry.SheafDerivedDG
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-!
# 準連接コホモロジーによる充満 dg 部分模型

概要：層複体の acyclic dg 商で、忘却後のコホモロジーが準連接な対象を取る。
方針：元の層複体のコホモロジーで対象条件を指定し、既存の充満 dg 部分圏を使う。
規約：平坦分解後の path 商を使う。H⁰ と既存 Dqc の同値は DqcDerivedComparison で証明する。
使われ方：KST D4・§13 決定11、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory AlgebraicGeometry
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：元の層複体の全コホモロジーを O 加群へ忘れると準連接になる条件。
方針：宇宙調整した複体を元へ戻してから実際のコホモロジーを取る。
規約：各項の準連接性は要求しない。
使われ方：KST D4、Toën §3.2 の D_qc の dg 対象条件。
-/
def complexHasQuasicoherentCohomology (K : B.Complexes) : Prop :=
  ∀ n : ℤ, (B.forget.obj ((B.complexLiftEquivalence.inverse.obj K).homology n)).IsQuasicoherent

/--
概要：acyclic dg 商の対象を準連接コホモロジーの条件で指定する。
方針：商の対象が保持する元の層複体に条件を課す。
規約：商の Hom や微分は変更しない。
使われ方：KST D4・§13 決定11の充満 dg 部分圏。
-/
def dqcDGObjects : Set B.DerivedDG := fun K =>
  B.complexHasQuasicoherentCohomology (B.resolvedAugmentation.obj K.val)

/--
概要：準連接コホモロジーを持つ対象による充満 dg 部分模型。
方針：層複体の実際の dg 商の充満部分圏を取る。
規約：実際の Dqc との H⁰ 比較は DqcDerivedComparison で証明済み。平坦分解はレーン計画 §26–28。
使われ方：KST D4・§13 決定11、Toën §3.2 の導来幾何の dg 模型。
-/
abbrev DqcDGModel := DGFullSubcategory B.DerivedDG B.dqcDGObjects

/--
概要：準連接コホモロジーの部分模型は既存 DGCategory の構造を持つ。
方針：商の Hom 複体・微分・合成をそのまま制限する。
規約：追加の公理や局所化の仮定を要求しない。
使われ方：KST D4、Toën §3.2 の局所化と降下の dg 入力。
-/
instance dqcDGModelCategory : DGCategory CoefficientDGBase.{u} B.DqcDGModel :=
  dgFullSubcategoryEnrichment CoefficientDGBase.{u} B.DerivedDG B.dqcDGObjects

/--
概要：準連接コホモロジーの dg 部分模型から層複体の dg 商への包含。
方針：既存の充満 dg 部分圏の包含を使う。
規約：各 Hom 複体上では恒等射。
使われ方：KST D4、Toën §3.2 の D_qc の包含の dg 模型。
-/
def dqcDGModelInclusion : DGFunctor CoefficientDGBase.{u} B.DqcDGModel B.DerivedDG :=
  dgFullSubcategoryInclusion CoefficientDGBase.{u} B.DerivedDG B.dqcDGObjects

variable [HasDerivedCategory.{w} B.Modules]

/--
概要：dg 対象条件は元の層複体の導来像が既存 Dqc の対象条件を満たすことと同値。
方針：Mathlib の導来コホモロジーと複体コホモロジーの比較同型で準連接性を移す。
規約：この対象条件の比較を後続の DqcDerivedComparison の関手と圏同値へ渡す。
使われ方：KST D4・§13 決定11、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/
lemma mem_dqcDGObjects_iff (K : B.DerivedDG) :
    K ∈ B.dqcDGObjects ↔ B.hasQuasicoherentCohomology
      ((DerivedCategory.Q (C := B.Modules)).obj
        (B.complexLiftEquivalence.inverse.obj (B.resolvedAugmentation.obj K.val))) := by
  let L := B.complexLiftEquivalence.inverse.obj (B.resolvedAugmentation.obj K.val)
  constructor
  · intro h n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (B.forget.mapIso ((DerivedCategory.homologyFunctorFactors B.Modules n).app L)).symm (h n)
  · intro h n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (B.forget.mapIso ((DerivedCategory.homologyFunctorFactors B.Modules n).app L)) (h n)

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
