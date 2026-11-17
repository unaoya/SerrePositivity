module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicTopology.CechNerve

/-!
概要：一つの開被覆から、実際の Čech nerve のタプル被覆を得る。
方針：同じ射影の逆像の有限交叉を取り、nerve の射影の合成則を使う。
規約：次数ごとに独立の被覆を選ばず、同じ添字の前合成を使う。
使われ方：射影 Čech の四角形を二重 Čech の可換な図式へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type} (U : ι → X.Opens)

/-- 同じ被覆の全射影による逆像の交叉を、実際の nerve の開とする。 -/
def schemeCechTupleOpen (n : SimplexCategoryᵒᵖ) (t : Fin (n.unop.len + 1) → ι) :
    ((Arrow.mk f).cechNerve.obj n).Opens :=
  ⨅ j, (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) j) ⁻¹ᵁ U (t j)

/-- 元の被覆が全体を覆えば、同じタプル開は各 nerve 項を覆う。 -/
theorem schemeCechTupleOpen_iSup (hc : (⨆ i, U i) = ⊤) (n : SimplexCategoryᵒᵖ) :
    (⨆ t, schemeCechTupleOpen f U n t) = ⊤ := by
  classical
  apply le_antisymm le_top
  intro x hx
  have hc' : ∀ j : Fin (n.unop.len + 1), ∃ i,
      (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) j).base x ∈ U i := by
    intro j
    have h : (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) j).base x ∈
        (⨆ i, U i) := by rw [hc]; trivial
    simpa only [Opens.mem_iSup] using h
  choose t ht using hc'
  apply Opens.mem_iSup.mpr
  refine ⟨t, ?_⟩
  change x ∈ ((⨅ j, (WidePullback.π
    (fun _ : Fin (n.unop.len + 1) ↦ f) j) ⁻¹ᵁ U (t j)) : Opens _)
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact ht

set_option backward.isDefEq.respectTransparency false in
/-- 実際の nerve の射は、同じ添字の前合成に沿うタプル被覆の細分を与える。 -/
theorem schemeCechTupleOpen_map_le {m n : SimplexCategoryᵒᵖ} (h : m ⟶ n)
    (t : Fin (m.unop.len + 1) → ι) :
    schemeCechTupleOpen f U m t ≤ ((Arrow.mk f).cechNerve.map h) ⁻¹ᵁ
      schemeCechTupleOpen f U n (fun j ↦ t (h.unop.toOrderHom j)) := by
  intro x hx
  change ((Arrow.mk f).cechNerve.map h).base x ∈
    ((⨅ j, (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) j) ⁻¹ᵁ
      U (t (h.unop.toOrderHom j))) : Opens _)
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  intro j
  have hj := (iInf_le (fun k ↦ (WidePullback.π
    (fun _ : Fin (m.unop.len + 1) ↦ f) k) ⁻¹ᵁ U (t k)) (h.unop.toOrderHom j)) hx
  have he : (Arrow.mk f).cechNerve.map h ≫
      WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) j =
        WidePullback.π (fun _ : Fin (m.unop.len + 1) ↦ f) (h.unop.toOrderHom j) := by
    change WidePullback.lift _
      (fun i : Fin (n.unop.len + 1) ↦ WidePullback.π
        (fun _ : Fin (m.unop.len + 1) ↦ f) (h.unop.toOrderHom i)) _ ≫ _ = _
    exact WidePullback.lift_π _ _ _ _ j
  change (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) j).base
    (((Arrow.mk f).cechNerve.map h).base x) ∈ U (t (h.unop.toOrderHom j))
  have hh : (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) j).base
      (((Arrow.mk f).cechNerve.map h).base x) =
      (WidePullback.π (fun _ : Fin (m.unop.len + 1) ↦ f) (h.unop.toOrderHom j)).base x := by
    calc
      _ = (((Arrow.mk f).cechNerve.map h) ≫
          WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) j).base x := rfl
      _ = _ := congrArg (fun k : (Arrow.mk f).cechNerve.obj m ⟶ X ↦ k.base x) he
  exact hh.symm ▸ hj

end SerrePositivity.AlgebraicGeometry
