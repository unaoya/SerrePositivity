module

public import SerrePositivity.KST.DerivedGeometry.SheafTriaHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
概要：層の acyclic 代表対象の三角閉包を Mathlib の acyclic 部分圏と同定する。
方針：片方向は三角閉包の最小性、逆方向は全対象の層複体表示と代表対象の比較を使う。
規約：各項が準連接であることや有界性を仮定しない。
使われ方：Drinfeld §2.4・Thm 3.4、KST D4・§10-7、Toën §3.2 の導来局所化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：元の層の acyclic ホモトピー部分圏を tria へ引き戻した対象条件。
方針：証明済みの三角同値の順関手による逆像を取る。
規約：元の層コホモロジーで acyclic を判定する。
使われ方：Drinfeld §2.4、KST D4 の acyclic 三角閉包の同定。
-/
def acyclicTriaPreimage : ObjectProperty (TriaCategory CoefficientDGBase.{u} B.Complexes) :=
  (_root_.HomotopyCategory.subcategoryAcyclic B.Modules).inverseImage
    B.triaHomotopyEquivalence.functor

/--
概要：acyclic 部分圏の tria への逆像は三角部分圏。
方針：三角関手による逆像の既存定理を使う。
規約：三角構造は既存のものを使う。
使われ方：Drinfeld §2.4、KST D4 の三角閉包の最小性。
-/
instance acyclicTriaPreimage_isTriangulated : B.acyclicTriaPreimage.IsTriangulated := by
  dsimp [acyclicTriaPreimage]; infer_instance

/--
概要：acyclic 部分圏の tria への逆像は同型で閉じる。
方針：既存の acyclic 部分圏の同型閉性を逆像へ移す。
規約：判定に代表の選択を持ち込まない。
使われ方：Drinfeld §2.4、KST D4 の対象の移送。
-/
instance acyclicTriaPreimage_closedUnderIso : B.acyclicTriaPreimage.IsClosedUnderIsomorphisms := by
  dsimp [acyclicTriaPreimage]; infer_instance

/--
概要：代表対象の逆像 acyclic 条件は元の層複体の acyclic 条件に一致する。
方針：代表対象の像の計算同型と Mathlib のホモトピー商での判定を使う。
規約：実際の同じ層複体のコホモロジーを取る。
使われ方：Drinfeld §2.4、KST D4・§10-7 の指定部分圏の比較。
-/
theorem acyclicTriaPreimage_representable_iff (K : B.Complexes) :
    B.acyclicTriaPreimage (triaRepresentable CoefficientDGBase.{u} B.Complexes K) ↔
      K ∈ B.acyclicComplexes :=
  ((_root_.HomotopyCategory.subcategoryAcyclic B.Modules).prop_iff_of_iso
    (B.triaHomotopyRepresentableIso K)).trans
      (_root_.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

/--
概要：acyclic 代表対象の三角閉包は Mathlib の acyclic 部分圏の逆像と一致する。
方針：最小性で片方向を示し、全対象の層複体表示と三角同値で逆向きを示す。
規約：冪等完備化や追加の局所化は使わない。
使われ方：Drinfeld §2.4・Thm 3.4、KST D4・§10-7 の Mathlib 導来圏との比較。
-/
theorem acyclicTriaImage_eq :
    triaImage CoefficientDGBase.{u} B.Complexes B.acyclicComplexes = B.acyclicTriaPreimage := by
  apply le_antisymm
  · apply (triaImage_le_iff_generators CoefficientDGBase.{u} B.Complexes
      B.acyclicComplexes B.acyclicTriaPreimage).mpr
    intro K hK
    exact (B.acyclicTriaPreimage_representable_iff K).mpr hK
  · intro Z hZ
    let E := B.triaHomotopyEquivalence
    let M := (E.functor.obj Z).as
    let K := B.complexLiftEquivalence.functor.obj M
    let e : E.functor.obj (triaRepresentable CoefficientDGBase.{u} B.Complexes K) ≅
        E.functor.obj Z :=
      B.triaHomotopyRepresentableIso K ≪≫
        (_root_.HomotopyCategory.quotient B.Modules (.up ℤ)).mapIso
          (B.complexLiftEquivalence.unitIso.app M).symm
    have hK : K ∈ B.acyclicComplexes :=
      (B.acyclicTriaPreimage_representable_iff K).mp
        ((_root_.HomotopyCategory.subcategoryAcyclic B.Modules).prop_of_iso e.symm hZ)
    exact (triaImage CoefficientDGBase.{u} B.Complexes B.acyclicComplexes).prop_of_iso
      (E.functor.preimageIso e)
      (triaImage_representable CoefficientDGBase.{u} B.Complexes B.acyclicComplexes K hK)

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
