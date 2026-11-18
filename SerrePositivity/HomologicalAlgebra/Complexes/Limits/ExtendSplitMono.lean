module

public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# 次数別の分裂単射の零延長

概要：複体の次数別分裂は次数形状の埋め込みに沿う零延長で保たれる。
方針：像の次数では延長の標準同型、像の外では零対象を使う。
規約：分裂の微分との可換性を仮定しない。
使われ方：正規化鎖の分裂を整数複体へ移す。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {I J : Type*} {c : ComplexShape I} {d : ComplexShape J}

lemma extendMap_degreewise_isSplitMono {K L : HomologicalComplex C c} (f : K ⟶ L)
    (hf : ∀ n, IsSplitMono (f.f n)) (e : c.Embedding d) (j : J) :
    IsSplitMono ((extendMap f e).f j) := by
  classical
  by_cases h : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := h
    let : IsSplitMono (f.f i) := hf i
    rw [extendMap_f f e hi]
    infer_instance
  · have hz : IsZero ((K.extend e).X j) :=
      isZero_extend_X K e j (fun i hi => h ⟨i, hi⟩)
    exact ⟨⟨{ retraction := 0, id := hz.eq_of_src _ _ }⟩⟩

end SerrePositivity.ComplexLimits
