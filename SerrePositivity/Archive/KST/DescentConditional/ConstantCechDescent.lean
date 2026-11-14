module

public import SerrePositivity.Archive.KST.DescentConditional.InitialCechDescent
public import SerrePositivity.Archive.KST.DescentConditional.CechReindexDescent
public import Mathlib.CategoryTheory.PUnit

/-!
# 終対象を持つ添字圏の定数図式の実降下

## 概要
終対象を持つ添字圏の定数図式の恒等増強が実際に降下することを証明する。

## 方針
終対象を選ぶ関手の左随伴を一対象圏への射影として構成する。
指定増強を保つ随伴添字変更と、一対象圏の始対象による降下判定を使う。

## 規約
前層の値の fibrancy を要求せず、指定比較そのものの弱同値を得る。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の非交和の被覆族。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K : Type u) [SmallCategory K]

/-- 概要：任意の値の定数図式の恒等増強（公理 (1)）。
方針：増強元と図式の全ての値を同じ空間に固定する。
規約：指定増強は恒等。使われ方：有限非交和の値と積の比較。 -/
def constantAugmentedCechSpace (X : SSet.{u}) : AugmentedCechDiagram K where
  left := X
  right := (Functor.const K).obj X
  hom := 𝟙 _

/-- 概要：一対象圏への射影は終対象を選ぶ関手の左随伴（公理 (1)）。
方針：単位は終対象への一意射、余単位は一対象圏の一意射とする。
規約：終対象が始対象である必要はない。使われ方：定数図式の実降下の添字変更。 -/
def terminalIndexAdjunction (k : K) (hk : IsTerminal k) :
    Functor.star K ⊣ (Functor.fromPUnit k : Discrete PUnit.{u + 1} ⥤ K) where
  unit :=
    { app n := hk.from n
      naturality {_n _m} _f := hk.hom_ext _ _ }
  counit :=
    { app _n := eqToHom (Subsingleton.elim _ _)
      naturality {_n _m} _f := Subsingleton.elim _ _ }
  left_triangle_components _n := Subsingleton.elim _ _
  right_triangle_components _n := hk.hom_ext _ _

variable [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{u})]

/-- 概要：終対象を持つ添字圏の定数図式の恒等増強は実際に降下（公理 (1)）。
方針：一対象圏の始対象の判定と、終対象による随伴添字変更を合成する。
規約：指定増強を保つ実際のホモトピー極限を使う。使われ方：被覆族の積の定数図式との比較。 -/
theorem constantAugmentedCechSpace_descent (k : K) (hk : IsTerminal k)
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
    (X : SSet.{u}) : HasCechSpaceDescent K I J (constantAugmentedCechSpace K X) := by
  let T := Discrete PUnit.{u + 1}
  let t : T := ⟨PUnit.unit⟩
  let ht : IsInitial t := IsInitial.ofUniqueHom
    (fun n ↦ eqToHom (Subsingleton.elim _ _)) (fun _ _ ↦ Subsingleton.elim _ _)
  have h : HasCechSpaceDescent T I J (constantAugmentedCechSpace T X) :=
    (cechSpaceDescent_initial_iff T t ht I J hcof _).mpr
      ((weakEquivalences SSet.{u}).id_mem X)
  exact (CechReindex.descent_iff K T I J (terminalIndexAdjunction K k hk) hcof
    (constantAugmentedCechSpace T X)).mp h

end SerrePositivity.KST.Descent
