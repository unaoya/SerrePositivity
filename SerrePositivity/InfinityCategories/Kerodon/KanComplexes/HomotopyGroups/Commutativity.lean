module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups

/-!
概要：高次ホモトピー群の可換性に用いる充填の比較。
方針：隣接する面の積を高次ホーンの充填で移す。
規約：Mathlib の MulStruct の積の向きを保持する。
使われ方：Kerodon Lemmas 3.2.3.7（Tag 00WA）–3.2.3.9（Tag 00WC） と Theorem 3.2.2.10。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.SimplexFaces
end SerrePositivity.KST.Spectra.SimplexFaces
namespace SerrePositivity.KST.Spectra.AdjacentProduct
end SerrePositivity.KST.Spectra.AdjacentProduct
namespace SerrePositivity.KST.Spectra.FourStruct
end SerrePositivity.KST.Spectra.FourStruct
namespace SerrePositivity.KST.Spectra.FourReduction
end SerrePositivity.KST.Spectra.FourReduction
namespace SerrePositivity.KST.Spectra.FourComparison
end SerrePositivity.KST.Spectra.FourComparison
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

namespace SimplexFaces
open _root_.SerrePositivity.KST.Spectra.SimplexFaces

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

/-- 概要：境界定数単体の退化の全ての面を計算する。
方針：RelStruct.refl の二つの指定面と残りの定数面を使う。
規約：j は退化単体の任意の面。
使われ方：Kerodon Example 3.2.3.6（Tag 00W9）。高次ホーンの互換性。 -/
theorem degenerate_face (f : X.PtSimplex n x) (i : Fin (n + 1)) (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ stdSimplex.σ i ≫ f.map =
      if j = i.castSucc ∨ j = i.succ then f.map else SSet.const x := by
  by_cases h₀ : j = i.castSucc
  · subst j
    rw [ite_eq_left (Or.inl rfl)]
    exact (PtSimplex.RelStruct.refl f i).δ_castSucc_map
  by_cases h₁ : j = i.succ
  · subst j
    rw [ite_eq_left (Or.inr rfl)]
    exact (PtSimplex.RelStruct.refl f i).δ_succ_map
  rw [ite_eq_right (by tauto)]
  by_cases hj : j < i.castSucc
  · exact (PtSimplex.RelStruct.refl f i).δ_map_of_lt j hj
  · exact (PtSimplex.RelStruct.refl f i).δ_map_of_gt j (by grind)

/-- 概要：積の充填の全ての面を計算する。
方針：三つの指定面と、それより外側の定数面に分ける。
規約：Mathlib の三面の順序 g、fg、f を保持する。
使われ方：Kerodon §3.2.3（Tag 00W3）。充填を組み合わせるホーンの互換性。 -/
theorem mul_face {f g fg : X.PtSimplex n x} {i : Fin n}
    (h : PtSimplex.MulStruct f g fg i) (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ h.map =
      if j = i.castSucc.castSucc then g.map else
      if j = i.castSucc.succ then fg.map else
      if j = i.succ.succ then f.map else SSet.const x := by
  by_cases h₀ : j = i.castSucc.castSucc
  · subst j; simp
  by_cases h₁ : j = i.castSucc.succ
  · subst j; simp [h₀]
  by_cases h₂ : j = i.succ.succ
  · subst j; simp [h₀, h₁]
  rw [ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂]
  by_cases hj : j < i.castSucc.castSucc
  · exact h.δ_map_of_lt j hj
  · exact h.δ_map_of_gt j (by grind)

end SimplexFaces

namespace AdjacentProduct
open _root_.SerrePositivity.KST.Spectra.AdjacentProduct

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
  {f g fg : X.PtSimplex (n + 2) x} {i : Fin (n + 1)}

/-- 概要：隣接する積の比較に使うホーンの面。
方針：積の充填と三つの退化単体を所定の四面へ置く。
規約：欠ける面は i + 3、定数でない面は i、i + 1、i + 2、i + 4。
使われ方：Kerodon Lemma 3.2.3.9（Tag 00WC） の特殊化。 -/
def face (h : PtSimplex.MulStruct f g fg i.succ) (j : Fin (n + 5)) :
    (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j = i.castSucc.castSucc.castSucc.castSucc then stdSimplex.σ i.succ.succ ≫ f.map else
  if j = i.castSucc.castSucc.castSucc.succ then h.map else
  if j = i.castSucc.castSucc.succ.succ then stdSimplex.σ i.castSucc.succ ≫ g.map else
  if j = i.succ.succ.succ.succ then stdSimplex.σ i.castSucc.castSucc ≫ f.map else
    SSet.const x

/-- 概要：隣接する積の比較ホーンの面は互換である。
方針：退化の二面と積の三面を計算し、有限順序の添字を照合する。
規約：i + 3 の面を除く全ての面。
使われ方：Kerodon Lemma 3.2.3.9（Tag 00WC）。Kan 充填の適用条件。 -/
theorem compatible (h : PtSimplex.MulStruct f g fg i.succ) :
    horn.IsCompatible (i := i.castSucc.succ.succ.succ) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.face h j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ i.val + 3 := by
    intro he
    apply hj
    apply Fin.ext
    simpa using he
  have hk' : k.val ≠ i.val + 3 := by
    intro he
    apply hk
    apply Fin.ext
    simpa using he
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.face]
  split_ifs <;> simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.coe_castPred,
         Fin.val_pred] at *
       omega)

/-- 概要：比較ホーンの欠ける面の全ての面を計算する。
方針：二面の交換公式で既知のホーン面へ移して計算する。
規約：φ は比較ホーンを充填する実際の単体。
使われ方：Kerodon Lemma 3.2.3.9（Tag 00WC）。隣接する積の反転。 -/
theorem output_face (h : PtSimplex.MulStruct f g fg i.succ)
    (φ : (Δ[n + 4] : SSet.{u}) ⟶ X)
    (hφ : ∀ (j : Fin (n + 5)) (_ : j ≠ i.castSucc.succ.succ.succ),
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.face h j) (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ stdSimplex.δ i.castSucc.succ.succ.succ ≫ φ =
      if j = i.castSucc.castSucc.castSucc then f.map else
      if j = i.castSucc.castSucc.succ then fg.map else
      if j = i.castSucc.succ.succ then g.map else SSet.const x := by
  by_cases hj : j ≤ i.castSucc.succ.succ
  · rw [stdSimplex.δ_comp_δ_assoc hj, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.face]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ] at *
         first | tauto | omega)
  · have hm : i.succ.succ.succ ≤ j := by grind
    have he : i.castSucc.succ.succ.succ = i.succ.succ.succ.castSucc := by
      apply Fin.ext; rfl
    rw [he, ← stdSimplex.δ_comp_δ_assoc hm, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.face]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ] at *
         first | tauto | omega)

/-- 概要：一つ後ろの面の積の充填から、因子を逆順にした隣接面の積の充填を得る。
方針：互換な四つの面を持つホーンを Kan 性で充填し、欠けた面を取る。
規約：次数は n + 2。i.castSucc と i.succ は隣接する積の添字。
使われ方：Kerodon Lemma 3.2.3.9（Tag 00WC）。高次群の可換性の前段。 -/
noncomputable def flip [KanComplex X] (h : PtSimplex.MulStruct f g fg i.succ) :
    PtSimplex.MulStruct g f fg i.castSucc where
  map := stdSimplex.δ i.castSucc.succ.succ.succ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.compatible h).liftOfKanComplex
  δ_castSucc_castSucc_map := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.output_face h _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.compatible h).δ_liftOfKanComplex j hj)]
    exact ite_eq_left rfl
  δ_succ_castSucc_map := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.output_face h _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.compatible h).δ_liftOfKanComplex j hj)]
    split_ifs <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
         first | tauto | omega)
  δ_succ_succ_map := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.output_face h _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.compatible h).δ_liftOfKanComplex j hj)]
    split_ifs <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
         first | tauto | omega)
  δ_map_of_lt j hj := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.output_face h _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.compatible h).δ_liftOfKanComplex j hj)]
    split_ifs <;> first | rfl | (exfalso; grind)
  δ_map_of_gt j hj := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.output_face h _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.compatible h).δ_liftOfKanComplex j hj)]
    split_ifs <;> first | rfl | (exfalso; grind)

end AdjacentProduct

/-- 概要：最後の四面の指定に用いる境界の族。
方針：最後の四面に a、b、c、d を置き、それ以前は定数とする。
規約：代表単体の次数は n + 2。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU） の可換性の証明。 -/
def fourFaces {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    (a b c d : X.PtSimplex (n + 2) x) (j : Fin (n + 4)) : (Δ[n + 2] : SSet.{u}) ⟶ X :=
  if j.val = n then a.map else
  if j.val = n + 1 then b.map else
  if j.val = n + 2 then c.map else
  if j.val = n + 3 then d.map else SSet.const x

/-- 概要：四つの指定面を持つ実際の高次単体。
方針：充填と、その境界の各面の等式を記録する。
規約：存在を仮定する界面ではなく、後で Kan ホーンから構成する幾何的なデータ。
使われ方：Kerodon Notation 3.2.3.1（Tag 00W4）。積の可換性の充填。 -/
structure FourStruct {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    (a b c d : X.PtSimplex (n + 2) x) where
  /-- 概要：指定した四面を持つ単体。
  方針：ホーンの充填から得る。
  規約：次数は n + 3。
  使われ方：Kerodon Notation 3.2.3.1（Tag 00W4）。 -/
  map : (Δ[n + 3] : SSet.{u}) ⟶ X
  /-- 概要：境界の全ての面の指定。
  方針：四つの面以外を定数にする。
  規約：面添字は零から n + 3。
  使われ方：Kerodon Notation 3.2.3.1（Tag 00W4）。充填の照合。 -/
  face_eq (j : Fin (n + 4)) : stdSimplex.δ j ≫ map = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces a b c d j

namespace FourStruct


variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

/-- 概要：a、定数、c を最後の三つの既知の面とする充填が存在する。
方針：最後の面を欠くホーンを充填し、その欠けた面を d とする。
規約：最後の四面は a、定数、c、d。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU） の可換性の証明。 -/
theorem exists_fill [KanComplex X] (a c : X.PtSimplex (n + 2) x) :
    ∃ d : X.PtSimplex (n + 2) x, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct a .const c d) := by
  let α (j : Fin (n + 4)) (_ : j ≠ Fin.last (n + 3)) : (Δ[n + 2] : SSet.{u}) ⟶ X :=
    if j.val = n then a.map else if j.val = n + 2 then c.map else SSet.const x
  have hαface (j) (hj) (k : Fin (n + 3)) : stdSimplex.δ k ≫ α j hj = SSet.const x := by
    dsimp [α]
    split_ifs <;> simp
  have hα : horn.IsCompatible α := fun _ _ _ _ _ ↦ by simp [hαface]
  let d : X.PtSimplex (n + 2) x :=
    { map := stdSimplex.δ (Fin.last (n + 3)) ≫ hα.liftOfKanComplex
      comm := by
        ext j : 1
        simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
        rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
          hα.δ_liftOfKanComplex _ (by simp)]
        exact hαface _ (Fin.castSucc_ne_last j) _ }
  refine ⟨d, ⟨{ map := hα.liftOfKanComplex, face_eq := ?_ }⟩⟩
  intro j
  induction j using Fin.lastCases with
  | last =>
    change d.map = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces a .const c d (Fin.last (n + 3))
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces]
  | cast j =>
    rw [hα.δ_liftOfKanComplex _ (by simp)]
    dsimp [α, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces]
    split_ifs <;> first | rfl | (exfalso; omega)

end FourStruct

namespace FourReduction
open _root_.SerrePositivity.KST.Spectra.FourReduction

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
  {a ia c d : X.PtSimplex (n + 2) x}

/-- 概要：四面の充填の最初の二面を逆元で消すためのホーンの面。
方針：逆元の積の充填、逆元の退化、元の四面、最後の面の退化を置く。
規約：欠ける面は n + 2。
使われ方：Kerodon Lemma 3.2.3.7（Tag 00WA） の最後の四面への特殊化。 -/
def face (h : PtSimplex.MulStruct a ia .const (Fin.last n).castSucc)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct a .const c d) (j : Fin (n + 5)) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j.val = n then h.map else
  if j.val = n + 1 then stdSimplex.σ (Fin.last n).castSucc.castSucc ≫ ia.map else
  if j.val = n + 3 then T.map else
  if j.val = n + 4 then stdSimplex.σ (Fin.last (n + 2)) ≫ d.map else SSet.const x

set_option maxHeartbeats 800000 in
-- 四面の展開後の全ての有限分岐を検査するため、既定の上限を拡張する。
/-- 概要：逆元による消去のホーンは互換な面を持つ。
方針：積・退化・指定四面の全ての面を展開して照合する。
規約：n + 2 の面を除く。
使われ方：Kerodon Lemma 3.2.3.7（Tag 00WA）。消去の充填。 -/
theorem compatible (h : PtSimplex.MulStruct a ia .const (Fin.last n).castSucc)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct a .const c d) :
    horn.IsCompatible (i := (Fin.last n).castSucc.castSucc.succ.succ)
      (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.face h T j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 2 := by
    intro he; apply hj; apply Fin.ext; simpa using he
  have hk' : k.val ≠ n + 2 := by
    intro he; apply hk; apply Fin.ext; simpa using he
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.face]
  split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face,
    T.face_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces, RelativeMorphism.const_map, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last,
         Fin.coe_castPred, Fin.val_pred] at *
       first | tauto | omega)

/-- 概要：消去ホーンの欠ける面の境界は通常の積の三面になる。
方針：二面の交換公式で既知の面へ移し、逆元の単位面を消す。
規約：φ は消去ホーンの充填。
使われ方：Kerodon Lemma 3.2.3.7（Tag 00WA）。四面から積の等式への変換。 -/
theorem output_face (h : PtSimplex.MulStruct a ia .const (Fin.last n).castSucc)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct a .const c d) (φ : (Δ[n + 4] : SSet.{u}) ⟶ X)
    (hφ : ∀ (j : Fin (n + 5)) (_ : j ≠ (Fin.last n).castSucc.castSucc.succ.succ),
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.face h T j) (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last n).castSucc.castSucc.succ.succ ≫ φ =
      if j.val = n + 1 then ia.map else
      if j.val = n + 2 then c.map else
      if j.val = n + 3 then d.map else SSet.const x := by
  by_cases hj : j ≤ (Fin.last n).castSucc.castSucc.succ
  · rw [stdSimplex.δ_comp_δ_assoc hj, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.face]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face,
      RelativeMorphism.const_map, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc,
           Fin.val_succ, Fin.val_last] at *
         first | tauto | omega)
  · have hm : (Fin.last n).castSucc.succ.succ ≤ j := by grind
    have he : (Fin.last n).castSucc.castSucc.succ.succ =
        (Fin.last n).castSucc.succ.succ.castSucc := by apply Fin.ext; rfl
    rw [he, ← stdSimplex.δ_comp_δ_assoc hm, hφ _ (by grind)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.face]
    split_ifs <;> try simp only [T.face_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, RelativeMorphism.const_map, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_iff_val_le_val, Fin.val_castSucc,
           Fin.val_succ, Fin.val_last] at *
         first | tauto | omega)

/-- 概要：四面 a、定数、c、d と逆元の充填から d と逆元の積 c を得る。
方針：消去ホーンを充填して欠ける面を取る。
規約：逆元の充填は一つ前の積の添字で与える。
使われ方：Kerodon Lemma 3.2.3.7（Tag 00WA）。四面の積の計算。 -/
noncomputable def mulStruct [KanComplex X]
    (h : PtSimplex.MulStruct a ia .const (Fin.last n).castSucc)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct a .const c d) : PtSimplex.MulStruct d ia c (Fin.last (n + 1)) where
  map := stdSimplex.δ (Fin.last n).castSucc.castSucc.succ.succ ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.compatible h T).liftOfKanComplex
  δ_castSucc_castSucc_map := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.output_face h T _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.compatible h T).δ_liftOfKanComplex j hj)]
    simp
  δ_succ_castSucc_map := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.output_face h T _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.compatible h T).δ_liftOfKanComplex j hj)]
    simp
  δ_succ_succ_map := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.output_face h T _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.compatible h T).δ_liftOfKanComplex j hj)]
    simp
  δ_map_of_lt j hj := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.output_face h T _ (fun j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.compatible h T).δ_liftOfKanComplex j hj)]
    split_ifs <;> first
      | rfl
      | (exfalso
         simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hj
         omega)
  δ_map_of_gt j hj := by exact (not_lt_of_ge (Fin.le_last j) hj).elim

/-- 概要：四面 a、定数、c、d を持つ充填は [d] = [c][a] を与える。
方針：a の左逆元で最初の二面を消去し、群の逆元消去を使う。
規約：商の積は最後の面で定義された積。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU） の可換性の証明。 -/
theorem class_eq [KanComplex X] (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct a .const c d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk d = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk c * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a := by
  obtain ⟨ia, ⟨hinv⟩⟩ := PtSimplex.MulStruct.exists_left_inverse a (Fin.last (n + 1))
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk ia * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a = 1 :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hinv
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk d * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk ia = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk c :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.mulStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip hinv) T)
  rw [← hc, mul_assoc, hi, mul_one]

end FourReduction

namespace FourComparison
open _root_.SerrePositivity.KST.Spectra.FourComparison

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
  {a c d d' : X.PtSimplex (n + 2) x}

/-- 概要：正順と逆順の四面の充填を比較するホーンの面。
方針：二つの充填の間に同じ単体の二つの退化を置く。
規約：最後の面を欠くホーン。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU） の可換性の最後のホーン。 -/
def face (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct a .const c d) (T' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct c .const a d')
    (j : Fin (n + 5)) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j.val = n then T.map else
  if j.val = n + 1 then stdSimplex.σ (Fin.last n).castSucc.castSucc ≫ a.map else
  if j.val = n + 2 then stdSimplex.σ (Fin.last n).castSucc.succ ≫ a.map else
  if j.val = n + 3 then T'.map else SSet.const x

set_option maxHeartbeats 800000 in
-- 四面と退化の組合せを展開した有限分岐の検査に既定の上限では不足する。
/-- 概要：積の順序を交換する比較ホーンの面は互換である。
方針：二つの充填の四面と退化の二面を直接照合する。
規約：最後の面以外を指定する。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU）。可換性の充填。 -/
theorem compatible (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct a .const c d) (T' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct c .const a d') :
    horn.IsCompatible (i := Fin.last (n + 4)) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.face T T' j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 4 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 4 := fun he ↦ hk (Fin.ext he)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.face]
  split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, T.face_eq, T'.face_eq,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces, RelativeMorphism.const_map, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last,
         Fin.coe_castPred, Fin.val_pred] at *
       first | tauto | omega)

/-- 概要：比較ホーンの最後の面は d、定数、定数、d' の四面を持つ。
方針：最後の面を取って各面を交換し、既知のホーンの面を計算する。
規約：正順と逆順の充填に同じ a、c を用いる。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU）。積の交換の比較。 -/
noncomputable def compare [KanComplex X]
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct a .const c d) (T' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct c .const a d') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct d .const .const d' where
  map := stdSimplex.δ (Fin.last (n + 4)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.compatible T T').liftOfKanComplex
  face_eq j := by
    rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.compatible T T').δ_liftOfKanComplex _ (by simp)]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.face, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces]
    split_ifs <;> try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face, T.face_eq, T'.face_eq,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces, RelativeMorphism.const_map, comp_const]
    all_goals (try split_ifs) <;> first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last,
           Fin.val_pred] at *
         first | tauto | omega)

end FourComparison

/-- 概要：二以上の次数のホモトピー群の積は可換。
方針：正順と逆順の四面の充填を比較し、その最後の面で積の等式を得る。
規約：KanHomotopyGroup の添字 n + 1 は実際の次数 n + 2 を表す。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU）、Goerss–Jardine I §7。L9a の可換性。 -/
theorem KanHomotopyGroup.mul_comm {X : SSet.{u}} [KanComplex X]
    {n : ℕ} {x : X _⦋0⦌} (a c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x) : a * c = c * a := by
  induction a using Quotient.inductionOn with | h a => ?_
  induction c using Quotient.inductionOn with | h c => ?_
  obtain ⟨d, ⟨T⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.exists_fill a c
  obtain ⟨d', ⟨T'⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.exists_fill c a
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.class_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.compare T T')
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.class_eq T
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.class_eq T'
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk c = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk c * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a
  simpa only [h₁, h₂, show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (RelativeMorphism.const : X.PtSimplex (n + 2) x) =
    (1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x) from rfl, one_mul] using he

/-- 概要：二以上の次数のホモトピー類は可換群をなす。
方針：既存の群構造にホーンで証明した可換性を加える。
規約：正次数群の添字 n + 1 に対応する実際の次数は n + 2。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU）。スペクトルの π_* のアーベル群。 -/
noncomputable instance instCommGroupKanHomotopyGroupHAddNatOfNat {X : SSet.{u}} [KanComplex X] {n : ℕ} {x : X _⦋0⦌} :
    CommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x) where
  __ := (inferInstance : Group (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))
  mul_comm := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_comm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.fourFaces := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.instCommGroupKanHomotopyGroupHAddNatOfNat (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.instCommGroupKanHomotopyGroupHAddNatOfNat := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.instCommGroupKanHomotopyGroupHAddNatOfNat

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.compatible := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.face (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.flip := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.output_face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.output_face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.compare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourComparison.compare := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.compare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourComparison.compatible := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.face (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourComparison.face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.class_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.class_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.compatible := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.face (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.mulStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.mulStruct := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.mulStruct

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.output_face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.output_face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.casesOn := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.exists_fill := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.exists_fill

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.face_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.face_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.map

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.mk := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.noConfusion := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.rec := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.recOn := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.mul_comm := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_comm

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexFaces.degenerate_face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexFaces.mul_face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.fourFaces.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fourFaces.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.face.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.face.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.flip._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.flip._proof_12 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.flip._proof_16 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip._proof_16

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.flip._proof_4 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.AdjacentProduct.flip._proof_7 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AdjacentProduct.flip._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourComparison.compare._proof_11 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.compare._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourComparison.face.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourComparison.face.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.face.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.face.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.mulStruct._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.mulStruct._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.mulStruct._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.mulStruct._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.mulStruct._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.mulStruct._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.mulStruct._proof_8 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.mulStruct._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourReduction.mulStruct._proof_9 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourReduction.mulStruct._proof_9

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.mk.inj := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FourStruct.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FourStruct.mk.sizeOf_spec
