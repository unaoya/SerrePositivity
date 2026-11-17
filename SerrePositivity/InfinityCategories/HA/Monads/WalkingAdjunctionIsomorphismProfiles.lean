module

public import Mathlib.Order.Preorder.Finite
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIntervalLaws

/-!
概要：元の実Homの同型は共通の有限順序の同型を与え、その点の値を保つ。
方針：元の逆射と全合成・単位則で実順序同型を構成する。
規約：同型性の反映や対象の等式を仮定しない。
使われ方：Riehl–Verity §4.1–§4.2の最初の併合の厳密な表示、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の退化の検出。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：有限順序の実同型は各点の自然数の値を保つ。
方針：有限個数を同一視し、厳密単調な有限自己写像の恒等性を使う。
規約：空の有限順序も含む。使われ方：Riehl–Verity §4.1の残余射の同型の表示。 -/
lemma ordinalOrderIso_val {m n : ℕ} (e : Fin m ≃o Fin n) (i : Fin m) :
    (e i).val = i.val := by
  have hmn : m = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
  subst n
  have he : (fun j => e j) = id := e.strictMono.eq_id
  exact congrArg Fin.val (congrFun he i)

/-- 概要：元の実Homの同型から共通表示の実順序同型を構成する。
方針：元の逆射の表示を逆写像にし、全単位・合成の法則を適用する。
規約：同じ元の射と逆射を使う。使われ方：Riehl–Verity §4.1の厳密な併合の検出。 -/
def walkingAdjunctionOrderIsoOfIsIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f] :
    Fin (walkingAdjunctionOrdinalCard X Y A) ≃o Fin (walkingAdjunctionOrdinalCard X Y B) :=
  OrderIso.ofHomInv (walkingAdjunctionOrderHom f) (walkingAdjunctionOrderHom (inv f))
    (by rw [← walkingAdjunctionOrderHom_comp, IsIso.inv_hom_id, walkingAdjunctionOrderHom_id])
    (by rw [← walkingAdjunctionOrderHom_comp, IsIso.hom_inv_id, walkingAdjunctionOrderHom_id])

/-- 概要：元の実Homの同型は点の個数を保つ。
方針：構成した実順序同型の有限個数を比較する。規約：四Homを含む。
使われ方：Riehl–Verity §4.1の残余射の厳密な表示。 -/
lemma walkingAdjunctionCard_eq_of_isIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f] :
    walkingAdjunctionOrdinalCard X Y A = walkingAdjunctionOrdinalCard X Y B := by
  simpa only [Fintype.card_fin] using
    Fintype.card_congr (walkingAdjunctionOrderIsoOfIsIso f).toEquiv

/-- 概要：元の実Homの同型の共通表示は全点の値を保つ。
方針：構成した実順序同型の値の法則を使う。規約：元の実射の全表示。
使われ方：Riehl–Verity §4.1の実残余射の同型の検出。 -/
lemma walkingAdjunctionOrderHom_val_of_isIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f]
    (i : Fin (walkingAdjunctionOrdinalCard X Y A)) :
    (walkingAdjunctionOrderHom f i).val = i.val :=
  ordinalOrderIso_val (walkingAdjunctionOrderIsoOfIsIso f) i

end SerrePositivity.InfinityCategories.HA.Monads
