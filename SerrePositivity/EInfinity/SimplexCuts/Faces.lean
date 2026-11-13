module

public import SerrePositivity.EInfinity.SimplexCuts.Outputs

/-!
# 一般の切断の面写像と非退化性

Berger–Fresse §2.2.1–6。各色の頂点列をその順序のまま単体圏の射とする。
すべての面が単射であることと、色・頂点の対が単射であることを照合する（5a-5a L03）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 全射語の一つの色の頂点列。退化した切断でも定義する。 -/
def vertices {m q r : ℕ} (s : Cut m q) (u : Surjection.Word r (m + 1)) (a : Fin r) :
    Fin (outputDegree s u a + 1) →o Fin (q + 1) where
  toFun i := s.vertical ((colorPositions s u.val a).orderEmbOfFin (colorPositions_card_eq s u a) i)
  monotone' := s.vertical.monotone.comp
    ((colorPositions s u.val a).orderEmbOfFin (colorPositions_card_eq s u a)).monotone

/-- 一つの色の出力単体から入力単体への面写像（BF §2.2.6）。 -/
def face {m q r : ℕ} (s : Cut m q) (u : Surjection.Word r (m + 1)) (a : Fin r) :
    (⦋outputDegree s u a⦌ : SimplexCategory) ⟶ ⦋q⦌ := SimplexCategory.mkHom (vertices s u a)

/-- L03 の証明の分割：非退化なら各色の頂点列は狭義単調。 -/
lemma vertices_strictMono {m q r : ℕ} {s : Cut m q} {u : Surjection.Word r (m + 1)}
    (h : Nondegenerate s u.val) (a : Fin r) : StrictMono (vertices s u a) := by
  intro i j hij
  have hi := (colorPositions s u.val a).orderEmbOfFin_mem (colorPositions_card_eq s u a) i
  have hj := (colorPositions s u.val a).orderEmbOfFin_mem (colorPositions_card_eq s u a) j
  exact vertex_strictMono_on_color h
    (((colorPositions s u.val a).orderEmbOfFin (colorPositions_card_eq s u a)).strictMono hij)
    ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

/-- 全色の面写像が単射であることが、切断の非退化性に等しい（BF §2.2.1）。 -/
lemma faces_mono_iff {m q r : ℕ} (s : Cut m q) (u : Surjection.Word r (m + 1)) :
    (∀ a, Mono (face s u a)) ↔ Nondegenerate s u.val := by
  constructor
  · intro h i j hij
    let a := label s u.val i
    have hi : i ∈ colorPositions s u.val a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hj : j ∈ colorPositions s u.val a :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (congrArg Prod.fst hij).symm⟩
    let e := (colorPositions s u.val a).orderIsoOfFin (colorPositions_card_eq s u a)
    let ii := e.symm ⟨i, hi⟩
    let jj := e.symm ⟨j, hj⟩
    have hei : (colorPositions s u.val a).orderEmbOfFin (colorPositions_card_eq s u a) ii = i :=
      congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)
    have hej : (colorPositions s u.val a).orderEmbOfFin (colorPositions_card_eq s u a) jj = j :=
      congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)
    have hv : vertices s u a ii = vertices s u a jj := by
      change s.vertical _ = s.vertical _
      rw [hei, hej]
      exact congrArg Prod.snd hij
    have heq : ii = jj := (SimplexCategory.mono_iff_injective.mp (h a)) hv
    exact hei.symm.trans ((congrArg
      ((colorPositions s u.val a).orderEmbOfFin (colorPositions_card_eq s u a)) heq).trans hej)
  · intro h a
    exact SimplexCategory.mono_iff_injective.mpr (vertices_strictMono h a).injective

end SerrePositivity.EInfinity.SimplexCuts
