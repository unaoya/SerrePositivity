module
public import SerrePositivity.KST.Fibration.FinSnocProductIso
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-! # 元の有限積の因子の局所化同型は同じ全有限積の局所化同型を与える -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の有限積の因子ごとの写像は、元の終端因子を取り出す積同型と厳密に可換。 -/
lemma finProduct_map_snoc {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    Limits.Pi.map (fun _ : Fin (n + 1) => f) ≫ (finSnocProductIso Y n).hom =
      (finSnocProductIso X n).hom ≫ (Limits.Pi.map (fun _ : Fin n => f) ⊗ₘ f) := by
  change Limits.Pi.map _ ≫ lift _ _ = lift _ _ ≫ _
  rw [comp_lift, lift_map]
  apply congrArg₂ lift
  · apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, Limits.Pi.map_π, Category.assoc, Limits.Pi.map_π,
      ← Category.assoc, Pi.lift_comp_π]
  · exact Limits.Pi.map_π _ _

/-- 元の空有限積の因子ごとの写像は厳密同型。 -/
def finEmptyProductMapIso {X Y : SSet.{u}} (f : X ⟶ Y) :
    (∏ᶜ fun _ : Fin 0 => X) ≅ (∏ᶜ fun _ : Fin 0 => Y) where
  hom := Limits.Pi.map (fun _ : Fin 0 => f)
  inv := Pi.lift (fun i => Fin.elim0 i)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  inv_hom_id := by
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i

/-- 各因子の同じ実写像の局所化同型性は、零因子を含む全有限積に保存される。 -/
theorem finProduct_map_anodyneQ_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Pi.map (fun _ : Fin n => f))) := by
  let Q := AnodyneHomotopy.anodyneQ
  induction n with
  | zero =>
    change IsIso (Q.map (finEmptyProductMapIso f).hom)
    infer_instance
  | succ n ih =>
    let v : (∏ᶜ fun _ : Fin n => X) ⟶ ∏ᶜ fun _ : Fin n => Y := Limits.Pi.map (fun _ => f)
    have hv : IsIso (Q.map v) := ih
    have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso v hv X
    have := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso f hf (∏ᶜ fun _ : Fin n => Y)
    have ht : IsIso (Q.map (v ⊗ₘ f)) := by
      rw [tensorHom_def, Q.map_comp]
      infer_instance
    have he := congrArg Q.map (finProduct_map_snoc f n)
    rw [Q.map_comp, Q.map_comp] at he
    have hi : IsIso (Q.map (Limits.Pi.map (fun _ : Fin (n + 1) => f)) ≫
        Q.map (finSnocProductIso Y n).hom) := by
      rw [he]
      change IsIso (Q.map (finSnocProductIso X n).hom ≫ Q.map (v ⊗ₘ f))
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hi

end SerrePositivity.KST.Fibration
