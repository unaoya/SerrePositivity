module

public import SerrePositivity.Archive.KST.DescentConditional.CechFiniteProducts

/-!
# 弱可縮な補成分を有限積から除く

## 概要
有限積のうち、終対象への射が弱同値となる因子を除く指定射が弱同値となることを証明する。

## 方針
補成分だけを終対象で置換する成分ごとの射を作り、有限積による弱同値保存を使う。
補成分が実際に終対象である積の指定射の逆を普遍性から構成する。

## 規約
除く因子の基点や収縮の指定は要求しない。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の非交和被覆の空の交叉の因子。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} [Finite ι]

/-- 概要：指定部分の添字だけを残す有限積の射（公理 (1)）。
方針：元の指定積射影を部分型で束ねる。
規約：元の値の同一視を含まない。使われ方：非定数の交叉の因子の除去。 -/
def finiteProductRestriction (X : ι → C) (p : ι → Prop) :
    (∏ᶜ X) ⟶ ∏ᶜ fun i : Subtype p ↦ X i :=
  Pi.lift fun i ↦ Pi.π X i

/-- 概要：補成分が終対象なら部分添字への指定射は同型（公理 (1)）。
方針：残す成分の射影と、補成分への一意射で指定逆を構成する。
規約：有限積の実際の指定射を用いる。使われ方：弱同値で補成分を終対象に置換した後の計算。 -/
def finiteProductRestrictionIso (X : ι → C) (p : ι → Prop)
    (ht : ∀ i, ¬ p i → IsTerminal (X i)) :
    (∏ᶜ X) ≅ ∏ᶜ fun i : Subtype p ↦ X i := by
  classical
  refine
    { hom := finiteProductRestriction X p
      inv := Pi.lift (fun i ↦ if h : p i then Pi.π (fun j : Subtype p ↦ X j) ⟨i, h⟩
        else (ht i h).from _)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Pi.hom_ext
    intro i
    by_cases h : p i
    · simp [finiteProductRestriction, h]
    · apply (ht i h).hom_ext
  · apply Pi.hom_ext
    intro i
    simp [finiteProductRestriction, i.property]

variable [ModelCategory SSet.{u}] [IsQuillenBifunctor (curriedTensor SSet.{u})]

/-- 概要：補成分が弱可縮なら部分添字への指定射は弱同値（公理 (1)）。
方針：補成分だけを終対象に置換した有限積の弱同値と、部分積への指定同型を比較する。
規約：因子の fibrancy や選んだ点は不要。使われ方：空の多重交叉の因子を実際の Čech 各段から除く。 -/
theorem finiteProductRestriction_weak
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
    (X : ι → SSet.{u}) (p : ι → Prop)
    (ht : ∀ i, ¬ p i → weakEquivalences SSet.{u} (terminal.from (X i))) :
    weakEquivalences SSet.{u} (finiteProductRestriction X p) := by
  classical
  let B : ι → SSet.{u} := fun i ↦ if p i then X i else ⊤_ SSet.{u}
  let f : ∀ i, X i ⟶ B i := fun i ↦
    if h : p i then eqToHom (by simp [B, h])
    else terminal.from (X i) ≫ eqToHom (by simp [B, h])
  have hf : ∀ i, weakEquivalences SSet.{u} (f i) := by
    intro i
    by_cases h : p i
    · dsimp only [f]
      rw [dite_eq_left h]
      exact mem_weakEquivalences _
    · dsimp only [f]
      rw [dite_eq_right h]
      exact (weakEquivalences SSet.{u}).comp_mem _ _ (ht i h) (mem_weakEquivalences _)
  have hb : ∀ i, ¬ p i → IsTerminal (B i) := by
    intro i h
    simpa only [B, ite_eq_right h] using (terminalIsTerminal : IsTerminal (⊤_ SSet.{u}))
  let e := finiteProductRestrictionIso B p hb
  have hs : ∀ i : Subtype p, IsIso (f i) := by
    intro i
    dsimp only [f]
    rw [dite_eq_left i.property]
    infer_instance
  have : IsIso (CategoryTheory.Limits.Pi.map (fun i : Subtype p ↦ f i)) := inferInstance
  have hn : CategoryTheory.Limits.Pi.map f ≫ e.hom =
      finiteProductRestriction X p ≫
        CategoryTheory.Limits.Pi.map (fun i : Subtype p ↦ f i) := by
    apply Pi.hom_ext
    intro i
    simp [e, finiteProductRestrictionIso, finiteProductRestriction]
  have hc := (weakEquivalences SSet.{u}).comp_mem _ _
    (cechFiniteProduct_weak hcof f hf) (mem_weakEquivalences e.hom)
  rw [hn] at hc
  exact (weakEquivalences SSet.{u}).of_postcomp _ _ (mem_weakEquivalences _) hc

end SerrePositivity.KST.Descent
