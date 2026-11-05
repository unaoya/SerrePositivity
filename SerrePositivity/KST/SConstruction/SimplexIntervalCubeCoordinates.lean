module
public import SerrePositivity.KST.SConstruction.SimplexIntervalCubicalOperators

/-! # 元の区間の面・退化の Bool 座標作用
概要：全単体作用素の区間 cube 作用を、元の像のファイバー上の max で回収する。
方針：一 bead の joint は両端だけで、その像は出力の非 joint 座標にならないことを使う。
規約：空ファイバーは零、複数元ファイバーは max。使われ方：native HA 成分の面・退化。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の一 bead 間の全端点保存射は、元の joint を同じ出力の joint に送る。 -/
lemma necklaceBeadMap_joint {d e : ℕ} (f : necklaceBead.{u} d ⟶ necklaceBead e)
    (v : (NecklaceShape.single d).Vertex) (hv : v.val ∈ (NecklaceShape.single d).joints) :
    (necklaceVertexMap f v).val ∈ (NecklaceShape.single e).joints := by
  have h : v = (NecklaceShape.single d).first ∨ v = (NecklaceShape.single d).last := by
    simp only [_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases h with rfl | rfl
  · exact (congrArg (fun w => w.val ∈ (NecklaceShape.single e).joints)
      (necklaceVertexMap_first f)).mpr (NecklaceShape.single e).zero_mem
  · exact (congrArg (fun w => w.val ∈ (NecklaceShape.single e).joints)
      (necklaceVertexMap_last f)).mpr (NecklaceShape.single e).last_mem

/-- 元の一 bead 間の cube 座標は、元の非 joint ファイバーの max だけで回収される。 -/
lemma necklaceBeadBooleanMap_coordinate {d e : ℕ}
    (f : necklaceBead.{u} d ⟶ necklaceBead e)
    (x : (NecklaceShape.single d).NonjointVertex → Bool)
    (w : (NecklaceShape.single e).NonjointVertex) :
    necklaceBooleanMap f x w = true ↔
      ∃ v : (NecklaceShape.single d).NonjointVertex,
        x v = true ∧ necklaceVertexMap f v.val = w.val := by
  exact (necklaceBooleanMap_coordinate f x w).trans
    ⟨fun h => h.elim
      (fun ⟨v, hv, he⟩ => False.elim
        (w.property (he ▸ necklaceBeadMap_joint f v hv))) _root_.id, Or.inr⟩

/-- 元の全単体作用素の区間座標は、元の局所頂点像の同じファイバー上の max。 -/
lemma simplexIntervalBooleanMap_coordinate {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b)
    (x : (NecklaceShape.single (b.val - a.val)).NonjointVertex → Bool)
    (w : (NecklaceShape.single
      ((θ.toOrderHom b).val - (θ.toOrderHom a).val)).NonjointVertex) :
    necklaceBooleanMap (simplexIntervalBeadMap.{u} θ a b hab) x w = true ↔
      ∃ v : (NecklaceShape.single (b.val - a.val)).NonjointVertex,
        x v = true ∧
          (θ.toOrderHom (simplexIntervalOrder a b hab v.val)).val - (θ.toOrderHom a).val =
            w.val.val := by
  apply (necklaceBeadBooleanMap_coordinate _ x w).trans
  constructor
  · rintro ⟨v, hv, he⟩
    exact ⟨v, hv, (simplexIntervalBeadMap_vertex θ a b hab v.val).symm.trans
      (congrArg Fin.val he)⟩
  · rintro ⟨v, hv, he⟩
    exact ⟨v, hv, Fin.ext ((simplexIntervalBeadMap_vertex θ a b hab v.val).trans he)⟩

/-- 元の一 bead 間の全 cube 作用は、元の全零 Bool 座標を全零座標へ送る。 -/
lemma necklaceBeadBooleanMap_zero {d e : ℕ} (f : necklaceBead.{u} d ⟶ necklaceBead e) :
    necklaceBooleanMap f (fun _ => false) = fun _ => false := by
  funext w
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨v, hv, _⟩ := (necklaceBeadBooleanMap_coordinate f _ w).mp h
  exact Bool.false_ne_true hv

end SerrePositivity.KST.SConstruction
