module

public import SerrePositivity.EInfinity.SimplexCuts.Expanded
public import Mathlib.Data.Fintype.EquivFin

/-!
# top degree の非退化切断の各色の次数

Berger–Fresse §2.2.6 の top degree の切断の支持の計算。
頂点数の等式と非退化性により、各色には全単体の全頂点が一度ずつ現れる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

lemma colorPositions_card_of_top {m q r : ℕ} {s : Cut m q} {u : Fin (m + 1) → Fin r}
    (h : Nondegenerate s u) (htop : m + q + 1 = r * (q + 1)) (a : Fin r) :
    (colorPositions s u a).card = q + 1 := by
  have hp : Function.Bijective (pair s u) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨h, by
      simpa only [Fintype.card_fin, Fintype.card_prod] using htop⟩
  have hf : Function.Bijective (fun i : colorPositions s u a => s.vertical i.val) := by
    constructor
    · intro i j hij
      apply Subtype.ext
      have hi : label s u i.val = a := (Finset.mem_filter.mp i.property).2
      have hj : label s u j.val = a := (Finset.mem_filter.mp j.property).2
      exact h (Prod.ext (hi.trans hj.symm) hij)
    · intro v
      obtain ⟨j, hj⟩ := hp.2 (a, v)
      exact ⟨⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.fst hj⟩⟩,
        congrArg Prod.snd hj⟩
  simpa using Fintype.card_of_bijective hf

end SerrePositivity.EInfinity.SimplexCuts
