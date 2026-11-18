module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Faces

/-!
模型。文献の定義との比較は後で
# 退化入力で潰れる切断の面

Berger–Fresse §2.2.6。L07 の証明の分割。
単体の隣接する二頂点を潰すとき、その間の垂直ステップを含む色の面は非単射になる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial

lemma face_comp_sigma_not_mono {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1))
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (i : Fin (q + 1)) :
    ∃ a, ¬Mono (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s u a ≫ SimplexCategory.σ i) := by
  let f : Finset (Fin (m + (q + 1) + 1)) :=
    Finset.univ.filter (fun j => i.val < (s.vertical j).val)
  have hf : f.Nonempty := by
    obtain ⟨j, hj⟩ := s.vertical_surjective i.succ
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hj]; exact Nat.lt_succ_self _⟩⟩
  let p := f.min' hf
  have hp : i.val < (s.vertical p).val := (Finset.mem_filter.mp (f.min'_mem hf)).2
  have hp0 : 0 < p.val := by
    by_contra h
    have he : p = 0 := by
      apply Fin.ext
      change p.val = 0
      omega
    rw [he, s.vertical_endpoints.1] at hp
    simp at hp
  let j : Fin (m + (q + 1)) := ⟨p.val - 1, by have hh := p.isLt; omega⟩
  have hjs : j.succ = p := Fin.ext (by dsimp [j]; omega)
  have hj : ¬i.val < (s.vertical j.castSucc).val := by
    intro h
    have hm : j.castSucc ∈ f := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hle := f.min'_le _ hm
    change p.val ≤ j.val at hle
    dsimp [j] at hle
    omega
  have hs := s.unit_step j
  have hstep : s.horizontal j.succ = s.horizontal j.castSucc ∧
      (s.vertical j.succ).val = (s.vertical j.castSucc).val + 1 := by
    rcases hs with hs | hs
    · have he := congrArg Fin.val hs.2
      rw [hjs] at he
      omega
    · exact hs
  have hvi : s.vertical j.castSucc = i.castSucc := by
    apply Fin.ext
    have he := hstep.2
    rw [hjs] at he
    change (s.vertical j.castSucc).val = i.val
    omega
  have hvj : s.vertical j.succ = i.succ := by
    apply Fin.ext
    have he := hstep.2
    rw [hvi] at he
    exact he
  let a := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u.val j.castSucc
  have ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u.val j.succ = a := congrArg u.val hstep.1
  have hmem0 : j.castSucc ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hmem1 : j.succ ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  let e := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a).orderIsoOfFin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s u a)
  let k := e.symm ⟨j.castSucc, hmem0⟩
  let l := e.symm ⟨j.succ, hmem1⟩
  have hk : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a).orderEmbOfFin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s u a) k =
      j.castSucc := congrArg Subtype.val (e.apply_symm_apply ⟨j.castSucc, hmem0⟩)
  have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a).orderEmbOfFin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s u a) l =
      j.succ := congrArg Subtype.val (e.apply_symm_apply ⟨j.succ, hmem1⟩)
  have hkvert : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s u a k = i.castSucc := by
    change s.vertical _ = _
    rw [hk, hvi]
  have hlvert : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s u a l = i.succ := by
    change s.vertical _ = _
    rw [hl, hvj]
  refine ⟨a, fun hmono => ?_⟩
  have hh : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s u a ≫ SimplexCategory.σ i).toOrderHom k =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s u a ≫ SimplexCategory.σ i).toOrderHom l := by
    change i.predAbove (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s u a k) = i.predAbove (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s u a l)
    rw [hkvert, hlvert]
    simp
  have hkl := (SimplexCategory.mono_iff_injective.mp hmono) hh
  have he := congrArg
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a).orderEmbOfFin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s u a)) hkl
  rw [hk, hl] at he
  exact (ne_of_lt j.castSucc_lt_succ) he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
