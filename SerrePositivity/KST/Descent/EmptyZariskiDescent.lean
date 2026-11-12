module

public import SerrePositivity.KST.Descent.ZariskiCechLaw
public import SerrePositivity.KST.Descent.TerminalCechDescent

/-!
# 空被覆から従う空対象上の値の弱可縮性

## 概要
公理 (1) の有限被覆族の降下から、空スキーム上の値の終対象への弱同値を証明する。

## 方針
空の添字を持つ実際の Zariski 被覆を構成し、各次数の空積の普遍性を使う。
終対象の実降下と指定増強を比較して増強元の弱同値を反映する。

## 規約
有限非交和の保存や空対象の値に関する追加の法則を仮定しない。

## 使われ方
論文 公理 (1)、補題 3.2・3.3。原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w t z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

/-- 概要：空の対象の空の有限 Zariski 被覆（公理 (1)）。
方針：添字を空にし、被覆条件は基礎点が存在しないことから証明する。
規約：有限型の圏内で定義。使われ方：空対象の値の降下。 -/
def emptyFiniteTypeZariskiCover {S : Scheme.{u}} (Y : FiniteTypeSchemes S)
    [IsEmpty Y.obj.left] : FiniteTypeZariskiCover Y where
  Index := PEmpty.{u + 1}
  finite := inferInstance
  obj i := i.elim
  inclusion i := i.elim
  openImmersion i := i.elim
  covers y := isEmptyElim y

/-- 概要：空被覆族の Čech 値は全次数で実際に終対象（公理 (1)）。
方針：添字の列から零番目の空の添字を取り出し、空積の一意性を直接証明する。
規約：前層の値の性質は要求しない。使われ方：空被覆の指定比較の検査。 -/
def familyCechValue_isTerminal_of_isEmpty
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    {ι : Type z} [Finite ι] [IsEmpty ι] {Y : C}
    (X : ι → C) (cover : ∀ i, X i ⟶ Y)
    {V : Type w} [Category.{t} V] [HasFiniteProducts V]
    (F : Cᵒᵖ ⥤ V) (n : SimplexCategory) :
    IsTerminal (familyCechValue X cover F n) := by
  refine IsTerminal.ofUniqueHom (fun Z ↦ Pi.lift (fun a ↦ isEmptyElim (a 0))) ?_
  intro Z f
  apply Pi.hom_ext
  intro a
  exact isEmptyElim (a 0)

variable {S : Scheme.{u}} [IsNoetherian S] [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：空対象上の元の前層の値から終対象への射は弱同値（公理 (1)）。
方針：実際の空 Zariski 被覆の降下を、各段が終対象であることと比較する。
規約：公理 (1) の帰結であり追加公理ではない。使われ方：非交和被覆の異なる成分の交叉を除く計算。 -/
theorem emptyZariskiValue_weak
    (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ SSet.{0}) [FiniteZariskiCechDescent I J F]
    (Y : FiniteTypeSchemes S) [IsEmpty Y.obj.left] :
    weakEquivalences SSet.{0} (terminal.from (F.obj (op Y))) := by
  let c := emptyFiniteTypeZariskiCover Y
  let : IsEmpty c.Index := (inferInstance : IsEmpty PEmpty.{u + 1})
  have h := FiniteZariskiCechDescent.descent (I := I) (J := J) (F := F) c
  apply cechSpaceSource_weak_of_descent_of_terminal_components SimplexCategory I J
    (familyCechSpace c.obj c.inclusion F) h
  intro n
  exact familyCechValue_isTerminal_of_isEmpty c.obj c.inclusion F n

end SerrePositivity.KST.Descent
