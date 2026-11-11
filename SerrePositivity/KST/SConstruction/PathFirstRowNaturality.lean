module
public import SerrePositivity.KST.SConstruction.PathFirstRow
public import SerrePositivity.KST.SConstruction.SOneComparison
public import SerrePositivity.KST.SConstruction.CofiberPostcompLaws

/-! # 経路の第一行比較の入力への自然性と一次段の照合
概要：入力の cofiber 保存射について比較は自然で、零次段は既存の S₁ 比較に一致する。
方針：第一行制限の後合成の式と、一点の内部 Hom の比較を使う。
規約：零対象の厳密な選択保存は不要。使われ方：反復構成と既存の構造射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：入力の射の後合成による経路の第一行の単体的写像。
方針：各内部 Hom に後合成し、前合成との自然性を使う。
規約：入力の射に保存条件は不要。使われ方：第一行比較の自然性の標的側。 -/
def pathFirstRowDiagramMap {C D : SSet.{u}} (f : C ⟶ D) :
    pathFirstRowDiagram C ⟶ pathFirstRowDiagram D where
  app d := (ihom (firstRowNerve (d.unop.len + 1))).map f
  naturality {_d _e} θ := (pre (pathFirstRowNerveFunctor.map θ.unop)).naturality f

/-- 概要：cofiber 保存射の後合成による S の経路構成の写像。
方針：全 gapped S の後合成と全単体作用素との可換性を使う。
規約：保存条件は cofiber と零対象。使われ方：第一行比較の自然性の源側。 -/
def pathSConstructionMap {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    simplicialPath (simplicialSConstruction C) ⟶ simplicialPath (simplicialSConstruction D) where
  app d := sPostcompCofiber (d.unop.len + 1) f hf
  naturality {d e} θ := (sPostcompCofiber_sMap (m := e.unop.len + 1) (n := d.unop.len + 1)
    f hf (SimplexPrefix.functor.map θ.unop).toOrderHom).symm

/-- 概要：経路の第一行制限は入力の cofiber 保存射について自然。
方針：各次数で元の第一行制限と後合成との可換式を使う。
規約：厳密な自然変換の等号。使われ方：反復中の自然な比較。 -/
lemma pathFirstRowRestriction_naturality {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    pathSConstructionMap f hf ≫ pathFirstRowRestriction D =
      pathFirstRowRestriction C ≫ pathFirstRowDiagramMap f := by
  apply NatTrans.ext
  funext d
  exact firstRowRestriction_sPostcompCofiber (d.unop.len + 1) f hf

/-- 概要：経路の零次の第一行比較は既存の S₁ 比較を回収する。
方針：第一行の一点の内部 Hom を元の圏へ同一視する。
規約：厳密等号。使われ方：一次方向の比較との照合。 -/
lemma pathFirstRowRestriction_zero (C : SSet.{u}) :
    (pathFirstRowRestriction C).app (Opposite.op ⦋0⦌) ≫ firstRowOneHomNatIso.hom.app C =
      sOneComparison C := rfl

/-- 概要：core の経路の零次比較は既存の core S₁ 比較を回収する。
方針：元の零次比較に core の合成法則を適用する。
規約：厳密等号。使われ方：反復の core の一次方向との照合。 -/
lemma corePathFirstRowRestriction_zero (C : SSet.{u}) :
    (corePathFirstRowRestriction C).app (Opposite.op ⦋0⦌) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (firstRowOneHomNatIso.hom.app C) = coreSOneComparison C := rfl

end SerrePositivity.KST.SConstruction
