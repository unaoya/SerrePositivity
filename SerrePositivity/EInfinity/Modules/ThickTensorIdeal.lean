module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Thick

/-!
# 加群準圏における厚いテンソルイデアル

概要：Mathew Definition 3.18 の厚いテンソルイデアルと生成閉包を定義する。
方針：安定準圏の共通の IsThick に、指定したテンソル関手による閉性だけを加える。
規約：テンソル関手の族を明示し、相対テンソルの構成や対称性を仮定の束にしない。
使われ方：BE 加群の相対テンソルが構成された後の descendability の定義。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open scoped Simplicial

/-- 概要：指定テンソル関手に関して閉じた厚い頂点条件（Mathew Definition 3.18）。
方針：共通の厚さに tensor の閉性だけを加える。
規約：tensorWith M は右から M とテンソルする全関手。
使われ方：一般の加群圏における descendability。 -/
structure IsThickTensorIdeal (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (tensorWith : C _⦋0⦌ → (C ⟶ C)) (P : C _⦋0⦌ → Prop) extends IsThick C P where
  /-- 任意の対象との指定テンソルで閉じる（Mathew Definition 3.18）。 -/
  tensor (x M : C _⦋0⦌) : P x → P ((tensorWith M).app _ x)

variable (C : SSet.{u}) [Quasicategory C] [IsStable C]
variable (tensorWith : C _⦋0⦌ → (C ⟶ C))

/-- 概要：一対象の生成する厚いテンソルイデアル（Mathew Definition 3.18）。
方針：その対象を含む全イデアルの交わり。
規約：単位対象の所属は後で定義する。使われ方：descendability。 -/
def thickTensorIdealGenerated (M : C _⦋0⦌) : C _⦋0⦌ → Prop :=
  fun N => ∀ P, IsThickTensorIdeal C tensorWith P → P M → P N

/-- 概要：生成された条件自体が厚いテンソルイデアル（Mathew Definition 3.18）。
方針：全てのイデアルの上界で各閉性を確認。
規約：元の tensorWith と retract を保持。使われ方：生成の普遍性。 -/
lemma generated_isThickTensorIdeal (M : C _⦋0⦌) :
    IsThickTensorIdeal C tensorWith (thickTensorIdealGenerated C tensorWith M) where
  zero h _P hP _ := hP.zero h
  iso e hx P hP hm := hP.iso e (hx P hP hm)
  cofiber t ht hx hy P hP hm := hP.cofiber t ht (hx P hP hm) (hy P hP hm)
  fiber t ht hx hy P hP hm := hP.fiber t ht (hx P hP hm) (hy P hP hm)
  retract r hy P hP hm := hP.retract r (hy P hP hm)
  tensor x N hx P hP hm := hP.tensor x N (hx P hP hm)

/-- 概要：生成元は生成したイデアルに属する（Mathew Definition 3.18）。
方針：任意の上界で与えられた所属を返す。
規約：同じ対象。使われ方：指数判定の生成元。 -/
lemma mem_generated (M : C _⦋0⦌) : thickTensorIdealGenerated C tensorWith M M :=
  fun _ _ h => h

end SerrePositivity.EInfinity.Modules
