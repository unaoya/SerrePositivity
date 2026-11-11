module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LocalizedPairBothEquality
public import SerrePositivity.KST.Fibration.FinSnocProductIso

/-! # 元の有限積への実際の射の全成分の局所化等号 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の有限積への実際の射を終端の積同型へ通すと、同じ全先行射影と最後の射影を得る。 -/
lemma finProduct_comp_snoc {P X : SSet.{u}} (n : ℕ)
    (f : P ⟶ ∏ᶜ fun _ : Fin (n + 1) => X) :
    f ≫ (finSnocProductIso X n).hom =
      lift (f ≫ Pi.lift (fun i : Fin n => Pi.π (fun _ : Fin (n + 1) => X) i.castSucc))
        (f ≫ Pi.π _ (Fin.last n)) := by
  change f ≫ lift _ _ = _
  rw [comp_lift]

/-- 元の有限積への二つの実際の射は、全成分が局所化で等しければ局所化で等しい。 -/
lemma finProduct_eq_of_anodyneQ_eq {P X : SSet.{u}} (n : ℕ)
    (f g : P ⟶ ∏ᶜ fun _ : Fin n => X)
    (h : ∀ i, AnodyneHomotopy.anodyneQ.map (f ≫ Pi.π _ i) =
      AnodyneHomotopy.anodyneQ.map (g ≫ Pi.π _ i)) :
    AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g := by
  induction n with
  | zero =>
    have he : f = g := by
      apply Pi.hom_ext
      intro i
      exact Fin.elim0 i
    exact congrArg AnodyneHomotopy.anodyneQ.map he
  | succ n ih =>
    have hp := ih
      (f ≫ Pi.lift (fun i : Fin n => Pi.π (fun _ : Fin (n + 1) => X) i.castSucc))
      (g ≫ Pi.lift (fun i : Fin n => Pi.π (fun _ : Fin (n + 1) => X) i.castSucc)) (by
        intro i
        simpa only [Category.assoc, Pi.lift_comp_π] using h i.castSucc)
    apply (cancel_mono (AnodyneHomotopy.anodyneQ.map (finSnocProductIso X n).hom)).1
    rw [← Functor.map_comp, ← Functor.map_comp, finProduct_comp_snoc, finProduct_comp_snoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pair_eq_of_anodyneQ_eq hp (h (Fin.last n))

end SerrePositivity.KST.Fibration
