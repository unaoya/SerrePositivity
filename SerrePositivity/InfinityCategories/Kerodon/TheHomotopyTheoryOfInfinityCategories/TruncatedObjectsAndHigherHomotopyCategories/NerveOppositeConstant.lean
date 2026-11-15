module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite

/-!
概要：元のnerveの反転同型の逆は、元の同じ対象の定値単体を保つ。
方針：元の計算できる反転射で同じ定値単体を計算し、同型の逆則で戻す。
規約：IS-W2 R02〜R03の既存反転・定値・逆の法則。追加の同型を選ばない。
使われ方：同じ二変数Hom∞入力の固定始域制限の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable (C : Type u) [SmallCategory C]

/-- 元の反転同型の同じ逆は、対象cの定値n単体をそのまま戻す。 -/
theorem nerveOppositeIso_inv_constant (c : C) (n : ℕ) :
    ((nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌))
      ((CategoryTheory.Functor.const (Fin (n+1))).obj (Opposite.op c)) =
        (CategoryTheory.Functor.const (Fin (n+1))).obj c := by
  let σ := (CategoryTheory.Functor.const (Fin (n+1))).obj c
  let τ := (CategoryTheory.Functor.const (Fin (n+1))).obj (Opposite.op c)
  have hr : nerveReverseChain σ = τ := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  change ((nerveOppositeIso (C := C)).hom.app (Opposite.op ⦋n⦌)) σ = τ at hr
  have h := congrArg (fun x => ((nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌)) x) hr
  change (((nerveOppositeIso (C := C)).hom ≫ (nerveOppositeIso (C := C)).inv).app
    (Opposite.op ⦋n⦌)) σ = _ at h
  rw [Iso.hom_inv_id] at h
  exact h.symm

/-- 同じ逆は、全定値単体の写像としても元の同じ頂点の定値写像を保つ。 -/
theorem nerveOppositeIso_inv_const {K : SSet.{u}} (c : C) :
    SSet.const (X := K) (nerveVertex (Opposite.op c)) ≫ (nerveOppositeIso (C := C)).inv =
      SSet.const (SSet.opObjEquiv.symm (nerveVertex c)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change ((nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌))
    ((CategoryTheory.Functor.const (Fin (n+1))).obj (Opposite.op c)) = _
  rw [nerveOppositeIso_inv_constant]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
