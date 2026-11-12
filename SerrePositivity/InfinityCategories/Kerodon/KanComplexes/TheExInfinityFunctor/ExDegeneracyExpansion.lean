module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExExpansionFaces
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionFrontCut
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionFrontDegeneracy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionRearDegeneracy

/-!
# 退化単体の拡張

概要：複雑度を指定した退化単体の拡張を通常の退化として表示する。
方針：元の単体と退化後の固定点の式を、Moss の切断した交換則へ代入する。
規約：Moss 2020 Lemma 28、Lemma 26 (8)・(9) を使う部分。
使われ方：pairing の対応先が非退化なら元も非退化であること。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：前側の面では複雑度の上界を一つ下げられる。
方針：前側の面の吸収則に元の固定点の式を代入する。
規約：Moss 2020 Lemma 28 の退化の元を面で復元する計算。
使われ方：前側の退化である単体の元の複雑度。
-/
theorem exComplexity_front_face (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (i : Fin (n + 2)) (hi : i ≤ k.castSucc) (s : (SSet.ex.obj X) _⦋n + 1⦌)
    (hs : s ∈ exComplexity X ⦋n + 1⦌ k.succ) :
    (SSet.ex.obj X).δ i s ∈ exComplexity X ⦋n⦌ k := by
  change subdivisionCutAt ⦋n⦌ k ≫ (SimplexCategory.sd.map (SimplexCategory.δ i) ≫ s.down) =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫ s.down
  change subdivisionCutAt ⦋n + 1⦌ k.succ ≫ s.down = s.down at hs
  calc
    _ = subdivisionCutAt ⦋n⦌ k ≫ (SimplexCategory.sd.map (SimplexCategory.δ i) ≫
        (subdivisionCutAt ⦋n + 1⦌ k.succ ≫ s.down)) := by rw [hs]
    _ = (subdivisionCutAt ⦋n⦌ k ≫ SimplexCategory.sd.map (SimplexCategory.δ i) ≫
        subdivisionCutAt ⦋n + 1⦌ k.succ) ≫ s.down := by simp only [Category.assoc]
    _ = (SimplexCategory.sd.map (SimplexCategory.δ i) ≫
        subdivisionCutAt ⦋n + 1⦌ k.succ) ≫ s.down :=
      congrArg (fun f => f ≫ s.down) (subdivisionCutAt_front_face_absorb n k i hi)
    _ = _ := by rw [Category.assoc, hs]

/--
概要：前側の退化の拡張は、元の拡張の通常の退化である。
方針：退化の前後の複雑度の固定点を Moss Lemma 26 (8) に代入する。
規約：Moss 2020 Lemma 28、h≤k の表示。
使われ方：退化単体の拡張の退化性。
-/
theorem exExpansion_front_degeneracy (X : SSet.{u}) (n : ℕ) (h k : Fin (n + 1))
    (hhk : h ≤ k) (t : (SSet.ex.obj X) _⦋n⦌)
    (ht : t ∈ exComplexity X ⦋n⦌ k)
    (hs : (SSet.ex.obj X).σ h t ∈ exComplexity X ⦋n + 1⦌ k.succ) :
    exExpansion X (n + 1) k.succ ((SSet.ex.obj X).σ h t) =
      (SSet.ex.obj X).σ h.castSucc (exExpansion X n k t) := by
  apply ULift.ext
  change subdivisionDegeneracyAt (n + 1) k.succ ≫
      (SimplexCategory.sd.map (SimplexCategory.σ h) ≫ t.down) =
    SimplexCategory.sd.map (SimplexCategory.σ h.castSucc) ≫
      (subdivisionDegeneracyAt n k ≫ t.down)
  change subdivisionCutAt ⦋n⦌ k ≫ t.down = t.down at ht
  change subdivisionCutAt ⦋n + 1⦌ k.succ ≫
    (SimplexCategory.sd.map (SimplexCategory.σ h) ≫ t.down) =
      SimplexCategory.sd.map (SimplexCategory.σ h) ≫ t.down at hs
  calc
    _ = subdivisionDegeneracyAt (n + 1) k.succ ≫
        (subdivisionCutAt ⦋n + 1⦌ k.succ ≫
          (SimplexCategory.sd.map (SimplexCategory.σ h) ≫ t.down)) := by rw [hs]
    _ = (subdivisionDegeneracyAt (n + 1) k.succ ≫
        subdivisionCutAt ⦋n + 1⦌ k.succ ≫
          SimplexCategory.sd.map (SimplexCategory.σ h)) ≫ t.down := by simp only [Category.assoc]
    _ = (SimplexCategory.sd.map (SimplexCategory.σ h.castSucc) ≫
        subdivisionDegeneracyAt n k ≫ subdivisionCutAt ⦋n⦌ k) ≫ t.down :=
      congrArg (fun f => f ≫ t.down) (subdivisionDegeneracyAt_front n h k hhk)
    _ = _ := by simp only [Category.assoc, ht]

/--
概要：後ろの退化の拡張は、元の拡張の一つ後ろの通常の退化である。
方針：退化の前後の複雑度の固定点を Moss Lemma 26 (9) に代入する。
規約：Moss 2020 Lemma 28、k≤h の表示。
使われ方：退化単体の拡張の退化性。
-/
theorem exExpansion_rear_degeneracy (X : SSet.{u}) (n : ℕ) (k h : Fin (n + 1))
    (hkh : k ≤ h) (t : (SSet.ex.obj X) _⦋n⦌)
    (ht : t ∈ exComplexity X ⦋n⦌ k)
    (hs : (SSet.ex.obj X).σ h t ∈ exComplexity X ⦋n + 1⦌ k.castSucc) :
    exExpansion X (n + 1) k.castSucc ((SSet.ex.obj X).σ h t) =
      (SSet.ex.obj X).σ h.succ (exExpansion X n k t) := by
  apply ULift.ext
  change subdivisionDegeneracyAt (n + 1) k.castSucc ≫
      (SimplexCategory.sd.map (SimplexCategory.σ h) ≫ t.down) =
    SimplexCategory.sd.map (SimplexCategory.σ h.succ) ≫
      (subdivisionDegeneracyAt n k ≫ t.down)
  change subdivisionCutAt ⦋n⦌ k ≫ t.down = t.down at ht
  change subdivisionCutAt ⦋n + 1⦌ k.castSucc ≫
    (SimplexCategory.sd.map (SimplexCategory.σ h) ≫ t.down) =
      SimplexCategory.sd.map (SimplexCategory.σ h) ≫ t.down at hs
  calc
    _ = subdivisionDegeneracyAt (n + 1) k.castSucc ≫
        (subdivisionCutAt ⦋n + 1⦌ k.castSucc ≫
          (SimplexCategory.sd.map (SimplexCategory.σ h) ≫ t.down)) := by rw [hs]
    _ = (subdivisionDegeneracyAt (n + 1) k.castSucc ≫
        subdivisionCutAt ⦋n + 1⦌ k.castSucc ≫
          SimplexCategory.sd.map (SimplexCategory.σ h)) ≫ t.down := by simp only [Category.assoc]
    _ = (SimplexCategory.sd.map (SimplexCategory.σ h.succ) ≫
        subdivisionDegeneracyAt n k ≫ subdivisionCutAt ⦋n⦌ k) ≫ t.down :=
      congrArg (fun f => f ≫ t.down) (subdivisionDegeneracyAt_rear n k h hkh)
    _ = _ := by simp only [Category.assoc, ht]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
