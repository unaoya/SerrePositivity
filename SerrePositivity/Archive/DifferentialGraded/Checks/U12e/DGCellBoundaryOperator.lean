module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Boundary
public import Mathlib.Data.ZMod.Basic

/-! # 任意次数cellのpath・境界作用素・Koszul符号の監査

## 概要
任意次数cellのpath・境界作用素・Koszul符号の監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

-- Hom直和の添字はcellの集合だけ。元のDのsmallnessは不要。
example (hD : localHomKFlat A D) (x y : D) :
    complexKFlat A (C.internalHom A D I x y) := C.internalHom_kFlat A D I hD x y

example (x y : D) : δ 1 2 (C.replacement A D I x y) = 0 := C.replacement_closed A D I x y

example (i : I) :
    (C.boundaryCochain A D I i).v (C.degree i) (C.degree i + 1) rfl
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
      (C.boundary i).val := C.boundaryCochain_generator A D I i

-- 正次数の生成元と異なる端点を許す。標数2にも対応する。
example (D : Type v) [DGCategory (ZMod 2) D] (x y : D)
    (z : complexCycles (ZMod 2) (homObject (ZMod 2) D x y) 8) :
    let C : Family (ZMod 2) D PUnit := ⟨fun _ => x, fun _ => y, fun _ => 7, fun _ => z⟩
    δ 1 2 (C.boundaryCochain (ZMod 2) D PUnit PUnit.unit) = 0 := by
  exact Family.boundaryCochain_closed _ _ _ _ _

#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.generator
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.term
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.generatorTerm
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.term_kFlat
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalHom
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.inclusion
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.originalHom
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.generatorInclusion
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalHom_ext
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalHom_kFlat
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.boundaryFamily
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.boundaryCochain
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.boundaryCochain_closed
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.boundaryCochain_generator
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceMiddle
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceMiddle_closed
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceMiddle_apply
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendMap
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFirst
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFirst_closed
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace_closed
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceSummand
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceSummand_closed
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceRow
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceRow_closed
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceRow_nil
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacementToShift
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement_closed
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement_precomp
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement_originalHom
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement_square_precomp
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement_square_originalHom
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement_square_singleton
