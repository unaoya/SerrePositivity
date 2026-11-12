module

public import SerrePositivity.KST.Descent.CechProductRestriction
public import SerrePositivity.KST.Descent.FamilyCechDiagonalComparison
public import SerrePositivity.KST.Descent.EmptyZariskiDescent

/-!
# 非交和被覆の指定対角比較の各段の弱同値

## 概要
公理 (1) から空の交叉の値を除き、非交和被覆の Čech 各段の対角比較が弱同値となることを証明する。

## 方針
定数添字の列の部分積への制限と、元の各成分の値への指定同型を合成する。

## 規約
元の前層の有限非交和保存は仮定しない。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の有限非交和保存の導出。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

/-- 概要：成分の添字と定数の添字の列の指定同値（公理 (1)）。
方針：定数の列と零番目の値を互いに逆にする。
規約：Čech の各段は少なくとも一座標を持つ。使われ方：定数の列の部分積の添字変更。 -/
def constantCechTupleEquiv (ι : Type z) (n : SimplexCategory) :
    ι ≃ {a : Fin (n.len + 1) → ι // ∀ j, a j = a 0} where
  toFun i := ⟨fun _ ↦ i, fun _ ↦ rfl⟩
  invFun a := a.val 0
  left_inv _ := rfl
  right_inv a := Subtype.ext (funext fun j ↦ (a.property j).symm)

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {ι : Type z} [Finite ι] {Y : C} (X : ι → C) (cover : ∀ i, X i ⟶ Y)
  [∀ i, Mono (cover i)] {V : Type w} [Category V] [HasFiniteProducts V]
  (F : Cᵒᵖ ⥤ V)

/-- 概要：定数の列の部分積と元の成分の値の積の指定同型（公理 (1)）。
方針：定数の列の添字変更と幾何の対角同型を同時に積へ写す。
規約：指定対角の引き戻しを hom に使う。使われ方：部分積への制限後の比較。 -/
def constantCechTupleProductIso (n : SimplexCategory) :
    (∏ᶜ fun a : {a : Fin (n.len + 1) → ι // ∀ j, a j = a 0} ↦
      F.obj (op (familyCechTerm X cover n a.val))) ≅ ∏ᶜ fun i ↦ F.obj (op (X i)) :=
  (Pi.whiskerEquiv (constantCechTupleEquiv ι n)
    (fun i ↦ F.mapIso (familyCechDiagonalIso X cover n i).symm.op)).symm

/-- 概要：指定対角射影は部分積への制限と指定同型の合成（公理 (1)）。
方針：元の各成分の積射影で指定射の合成を計算する。
規約：実際の比較の等式。使われ方：部分積の弱同値を対角比較へ渡す。 -/
theorem constantCechTupleProductIso_fac (n : SimplexCategory) :
    finiteProductRestriction
        (fun a : Fin (n.len + 1) → ι ↦ F.obj (op (familyCechTerm X cover n a)))
        (fun a ↦ ∀ j, a j = a 0) ≫ (constantCechTupleProductIso X cover F n).hom =
      familyCechDiagonalProjection X cover F n := by
  apply Pi.hom_ext
  intro i
  simp [finiteProductRestriction, constantCechTupleProductIso, Pi.whiskerEquiv,
    familyCechDiagonalProjection, constantCechTupleEquiv]

variable {S : Scheme.{u}} [IsNoetherian S] [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：非交和被覆の各段の対角比較は弱同値（公理 (1)）。
方針：非定数の列の空の交叉の値を除く有限積の弱同値と、定数の列の指定同型を合成する。
規約：前層の非交和保存を前提にしない。使われ方：公理 (1) による元の非交和の値の比較。 -/
theorem disjointFamilyCechDiagonalProjection_weak
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    {κ : Type u} [Finite κ] (A : κ → FiniteTypeSchemes S)
    (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ SSet.{0}) [FiniteZariskiCechDescent I J F]
    (n : SimplexCategory) :
    weakEquivalences SSet.{0}
      (familyCechDiagonalProjection A (fun i ↦ Sigma.ι A i) F n) := by
  have ht : ∀ a : Fin (n.len + 1) → κ, ¬ (∀ j, a j = a 0) →
      weakEquivalences SSet.{0}
        (terminal.from (F.obj (op (familyCechTerm A (fun i ↦ Sigma.ι A i) n a)))) := by
    intro a ha
    obtain ⟨j, hj⟩ := not_forall.mp ha
    let h := disjointFamilyCech_isInitial A n a j 0 hj
    let hs := h.isInitialObj (finiteTypeSchemesForget S)
      (familyCechTerm A (fun i ↦ Sigma.ι A i) n a)
    let : IsEmpty (familyCechTerm A (fun i ↦ Sigma.ι A i) n a).obj.left :=
      AlgebraicGeometry.isInitial_iff_isEmpty.mp ⟨hs⟩
    exact emptyZariskiValue_weak I J F _
  have hw := finiteProductRestriction_weak hcof
    (fun a : Fin (n.len + 1) → κ ↦
      F.obj (op (familyCechTerm A (fun i ↦ Sigma.ι A i) n a)))
    (fun a ↦ ∀ j, a j = a 0) ht
  let e := constantCechTupleProductIso A (fun i ↦ Sigma.ι A i) F n
  have hc := (weakEquivalences SSet.{0}).comp_mem _ _ hw (mem_weakEquivalences e.hom)
  rw [constantCechTupleProductIso_fac] at hc
  exact hc

end SerrePositivity.KST.Descent
