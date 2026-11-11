module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExPairingStep
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionFrontFace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionFaceDegeneracy

/-!
# Ex の拡張の前後の面

概要：指定面より前の面では複雑度が下がり、後ろの面は面の拡張に一致する。
方針：Moss Lemma 26 (2)・(3) を細分からの射への前合成に適用する。
規約：Moss 2020 Lemma 29 の前後の面の計算。
使われ方：pairing の指定面の一意性と先行関係の正則性。

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
概要：正の閾値で拡張した単体の前側の面は、一つ小さい閾値で固定される。
方針：元の単体の固定点の式を挿入して、前側の面の吸収則を使う。
規約：Moss 2020 Lemma 29、i≤k の場合。
使われ方：指定した面より前の面の最小複雑度が厳しく下がること。
-/
theorem exExpansion_front_complexity (X : SSet.{u}) (n : ℕ) (h : Fin (n + 1))
    (i : Fin (n + 3)) (hi : i ≤ h.succ.castSucc)
    (s : (SSet.ex.obj X) _⦋n + 1⦌) (hs : s ∈ exComplexity X ⦋n + 1⦌ h.succ) :
    (SSet.ex.obj X).δ i (exExpansion X (n + 1) h.succ s) ∈
      exComplexity X ⦋n + 1⦌ h.castSucc := by
  change subdivisionCutAt ⦋n + 1⦌ h.castSucc ≫
      (SimplexCategory.sd.map (SimplexCategory.δ i) ≫
        (subdivisionDegeneracyAt (n + 1) h.succ ≫ s.down)) =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫
      (subdivisionDegeneracyAt (n + 1) h.succ ≫ s.down)
  change subdivisionCutAt ⦋n + 1⦌ h.succ ≫ s.down = s.down at hs
  calc
    _ = subdivisionCutAt ⦋n + 1⦌ h.castSucc ≫
        (SimplexCategory.sd.map (SimplexCategory.δ i) ≫
          (subdivisionDegeneracyAt (n + 1) h.succ ≫
            (subdivisionCutAt ⦋n + 1⦌ h.succ ≫ s.down))) := by rw [hs]
    _ = (subdivisionCutAt ⦋n + 1⦌ h.castSucc ≫
        SimplexCategory.sd.map (SimplexCategory.δ i) ≫
          subdivisionDegeneracyAt (n + 1) h.succ ≫
            subdivisionCutAt ⦋n + 1⦌ h.succ) ≫ s.down := by simp only [Category.assoc]
    _ = (SimplexCategory.sd.map (SimplexCategory.δ i) ≫
        subdivisionDegeneracyAt (n + 1) h.succ ≫
          subdivisionCutAt ⦋n + 1⦌ h.succ) ≫ s.down :=
      congrArg (fun f => f ≫ s.down) (subdivisionDegeneracyAt_front_absorb n h i hi)
    _ = _ := by simp only [Category.assoc, hs]

/--
概要：指定面より後ろの面は、元の単体の一つ前の面を拡張したものに等しい。
方針：細分上の後ろの面との交換則を前合成に使う。
規約：Moss 2020 Lemma 29、i≥k+2 の場合。
使われ方：後ろの面は型 I または退化単体であること。
-/
theorem exExpansion_rear_face (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (j : Fin (n + 2)) (hkj : k.castSucc < j)
    (s : (SSet.ex.obj X) _⦋n + 1⦌) :
    (SSet.ex.obj X).δ j.succ (exExpansion X (n + 1) k.castSucc s) =
      exExpansion X n k ((SSet.ex.obj X).δ j s) := by
  apply ULift.ext
  change SimplexCategory.sd.map (SimplexCategory.δ j.succ) ≫
      (subdivisionDegeneracyAt (n + 1) k.castSucc ≫ s.down) =
    subdivisionDegeneracyAt n k ≫ (SimplexCategory.sd.map (SimplexCategory.δ j) ≫ s.down)
  rw [← Category.assoc, subdivisionDegeneracyAt_face_right n k j hkj, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
