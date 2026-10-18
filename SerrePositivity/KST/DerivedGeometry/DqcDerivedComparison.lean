module

public import SerrePositivity.KST.DerivedGeometry.SheafDerivedComparisonObjects
public import SerrePositivity.KST.DerivedGeometry.DqcDGModel

/-!
概要：準連接コホモロジーで制限した層の dg 増強の H⁰ を実際の Dqc と比較する。
方針：全層複体の導来比較の対象計算でコホモロジー条件を移し、充満部分圏へ制限する。
規約：項ごとの準連接性で置き換えず、元の層コホモロジーで判定する。
使われ方：KST D4・§10-7・§13 決定11、Drinfeld Lemma 13.5・Thm 3.4、Toën §3.2。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory AlgebraicGeometry
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) [HasDerivedCategory.{w} B.Modules]

/--
概要：商の dg 対象の準連接条件は実際の導来比較の像の条件と一致する。
方針：対象ごとの導来像の同型と既存のコホモロジー比較を合成する。
規約：同じ元の層複体のコホモロジーを読む。
使われ方：KST D4・§10-7、Drinfeld Thm 3.4、Toën §3.2 の Dqc への制限。
-/
theorem dqcDGObject_image_iff (K : B.DerivedDG) :
    K ∈ B.dqcDGObjects ↔ B.hasQuasicoherentCohomology
      (B.derivedDGHomotopyEquivalence.functor.obj
        ((toHomotopy CoefficientDGBase.{u} B.DerivedDG).obj
          (ForgetEnrichment.of (Complex CoefficientDGBase.{u}) K))) :=
  (B.mem_dqcDGObjects_iff K).trans
    (B.hasQuasicoherentCohomology.prop_iff_of_iso
      (B.derivedDGHomotopyEquivalence_objIso K.val)).symm

/--
概要：Dqc の dg 模型の H⁰ から元の層導来圏への実際の比較関手。
方針：充満 dg 部分圏の H⁰ 包含と全複体の導来同値を合成する。
規約：新たな局所化や三角閉包を取らない。
使われ方：KST D4、Drinfeld §2.4・Thm 3.4、Toën §3.2。
-/
def dqcDGToDerived : HomotopyCategory CoefficientDGBase.{u} B.DqcDGModel ⥤
    _root_.DerivedCategory B.Modules :=
  B.dqcDGModelInclusion.onHomotopy ⋙ B.derivedDGHomotopyEquivalence.functor

/--
概要：Dqc の dg 模型からの比較関手の像は準連接コホモロジーを持つ。
方針：各 H⁰ 対象を同じ dg 対象で表示し、証明済みの対象条件の同値を使う。
規約：同型により閉じた実際の Dqc の対象条件を使う。
使われ方：KST D4・§13 決定11、Toën §3.2。
-/
theorem dqcDGToDerived_mem (T : HomotopyCategory CoefficientDGBase.{u} B.DqcDGModel) :
    B.hasQuasicoherentCohomology (B.dqcDGToDerived.obj T) := by
  obtain ⟨T⟩ := T
  let M : B.DqcDGModel := ForgetEnrichment.to (Complex CoefficientDGBase.{u}) T
  exact (B.dqcDGObject_image_iff M.val).mp M.property

/--
概要：Dqc の dg 模型の H⁰ から実際の Dqc への関手。
方針：全導来比較を準連接コホモロジーの充満部分圏へ制限する。
規約：Dqc は元の層導来圏の充満部分圏。
使われ方：KST D4・§10-7、Toën §3.2 の導来幾何の増強。
-/
def dqcDGToDqc : HomotopyCategory CoefficientDGBase.{u} B.DqcDGModel ⥤ B.Dqc :=
  B.hasQuasicoherentCohomology.lift B.dqcDGToDerived B.dqcDGToDerived_mem

/--
概要：Dqc への比較関手は充満。
方針：充満 dg 部分圏の H⁰ 包含と導来同値の充満性を制限する。
規約：射の追加の商は取らない。
使われ方：KST D4、Drinfeld §2.4、Toën §3.2 の増強の同値。
-/
instance dqcDGToDqc_full : B.dqcDGToDqc.Full := by
  dsimp [dqcDGToDqc, dqcDGToDerived, dqcDGModelInclusion]
  infer_instance

/--
概要：Dqc への比較関手は忠実。
方針：充満 dg 部分圏の H⁰ 包含と導来同値の忠実性を制限する。
規約：元の H⁰ の射の等式を反映する。
使われ方：KST D4、Drinfeld §2.4、Toën §3.2 の増強の同値。
-/
instance dqcDGToDqc_faithful : B.dqcDGToDqc.Faithful := by
  dsimp [dqcDGToDqc, dqcDGToDerived, dqcDGModelInclusion]
  infer_instance

/--
概要：Dqc への比較関手は本質的全射。
方針：全導来圏の同値で対象を戻し、対象計算により同じ準連接条件を確認する。
規約：準連接な各項を持つ複体の存在を仮定しない。
使われ方：KST D4・§10-7・§13 決定11、Toën §3.2。
-/
instance dqcDGToDqc_essSurj : B.dqcDGToDqc.EssSurj where
  mem_essImage Y := by
    let E := B.derivedDGHomotopyEquivalence
    let T := E.functor.objPreimage Y.obj
    let K : B.DerivedDG := ForgetEnrichment.to (Complex CoefficientDGBase.{u}) T.as
    let e : E.functor.obj T ≅ Y.obj := E.functor.objObjPreimageIso Y.obj
    have h : B.hasQuasicoherentCohomology (E.functor.obj T) :=
      B.hasQuasicoherentCohomology.prop_of_iso e.symm Y.property
    have hK : K ∈ B.dqcDGObjects := (B.dqcDGObject_image_iff K).mpr h
    let M : B.DqcDGModel := ⟨K, hK⟩
    refine ⟨(toHomotopy CoefficientDGBase.{u} B.DqcDGModel).obj
      (ForgetEnrichment.of (Complex CoefficientDGBase.{u}) M), ⟨?_⟩⟩
    exact B.hasQuasicoherentCohomology.isoMk e

/--
概要：Dqc の dg 模型の H⁰ と実際の Dqc の比較関手は圏同値。
方針：完全忠実性と対象計算による本質的全射性を束ねる。
規約：証明済みの同じ比較関手を使う。
使われ方：KST D4、Drinfeld Lemma 13.5・Thm 3.4、Toën §3.2。
-/
instance dqcDGToDqc_isEquivalence : B.dqcDGToDqc.IsEquivalence where

/--
概要：層複体の acyclic dg 商の準連接部分模型は実際の Dqc の dg 増強。
方針：半自由分解と K-flat な商の証明から得た同じ導来比較を制限する。
規約：H⁰ を Dqc に定義し直さず、実際の二つの圏の同値を証明する。
使われ方：KST D4・§10-7・§13 決定11、Drinfeld Lemma 13.5・Thm 3.4、Toën §3.2。
-/
def dqcDGHomotopyEquivalence : HomotopyCategory CoefficientDGBase.{u} B.DqcDGModel ≌ B.Dqc :=
  B.dqcDGToDqc.asEquivalence

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
