module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.CutDegeneracy

/-!
# 切断した拡張退化と後ろの退化

概要：切断後の拡張退化と後ろの通常の退化の交換を証明する。
方針：和集合保存で singleton に帰着し、初期区間の全射像を計算する。
規約：Moss 2020 Lemma 26 (9)。原典と同じ生成元による証明。
使われ方：Ex の pairing が退化単体を退化単体へ送ること。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder

/--
概要：後ろの退化は切断した拡張退化を一つ下の次元へ移す。
方針：singleton の像の二つの場合を揃え、通常の退化の恒等式を使う。
規約：Moss 2020 Lemma 26 (9)、有限鎖上の式。
使われ方：細分上の退化との交換則。
-/
theorem finiteChainDegeneracy_rear (n : ℕ) (k h : Fin (n + 1)) (hkh : k ≤ h) :
    ((fun s => s.map (liftedDegeneracy n h)) ∘ finiteChainCut (n + 1) (ULift.up k.castSucc) ∘
        finiteChainDegeneracy.{u} (n + 1) k.castSucc) =
      (finiteChainCut n (ULift.up k) ∘ finiteChainDegeneracy n k ∘
        fun s => s.map (liftedDegeneracy (n + 1) h.succ)) := by
  apply finiteChainUnion_ext
    (((finiteChainMap_preservesUnion (liftedDegeneracy n h)).comp
      (finiteChainCut_preservesUnion (n + 1) (ULift.up k.castSucc))).comp
      (finiteChainDegeneracy_preservesUnion (n + 1) k.castSucc))
    (((finiteChainCut_preservesUnion n (ULift.up k)).comp
      (finiteChainDegeneracy_preservesUnion n k)).comp
      (finiteChainMap_preservesUnion (liftedDegeneracy (n + 1) h.succ)))
  intro i
  change (finiteChainCut (n + 1) (ULift.up k.castSucc)
      (finiteChainDegeneracy (n + 1) k.castSucc (finiteChainSingleton i))).map
      (liftedDegeneracy n h) =
    finiteChainCut n (ULift.up k) (finiteChainDegeneracy n k
      ((finiteChainSingleton i).map (liftedDegeneracy (n + 1) h.succ)))
  rw [finiteChainMap_singleton, finiteChainCutDegeneracy_singleton,
    finiteChainCutDegeneracy_singleton]
  have hv : liftedDegeneracy n h (liftedDegeneracy (n + 1) k.castSucc i) =
      liftedDegeneracy n k (liftedDegeneracy (n + 1) h.succ i) := by
    apply ULift.ext
    exact congrArg
      (fun f : SimplexCategory.mk (n + 2) ⟶ SimplexCategory.mk n => f i.down)
      (SimplexCategory.σ_comp_σ hkh)
  by_cases hi : i ≤ ULift.up k.castSucc.castSucc
  · rw [ite_eq_left hi,
      ite_eq_left ((liftedDegeneracy_le_castSucc_iff n k h hkh i).mpr hi),
      finiteChainMap_singleton, hv]
  · rw [ite_eq_right hi,
      ite_eq_right (fun hh => hi ((liftedDegeneracy_le_castSucc_iff n k h hkh i).mp hh)),
      finiteChainInitialSegment_map _ (liftedDegeneracy_surjective n h), hv]

/--
概要：細分上の後ろの退化は切断した拡張退化と交換する。
方針：有限鎖上の式を nerve の各頂点に適用する。
規約：Moss 2020 Lemma 26 (9)、k≤h。
使われ方：pairing の退化性の検証。
-/
@[reassoc] theorem subdivisionDegeneracyAt_rear (n : ℕ) (k h : Fin (n + 1)) (hkh : k ≤ h) :
    subdivisionDegeneracyAt.{u} (n + 1) k.castSucc ≫
      subdivisionCutAt (SimplexCategory.mk (n + 1)) k.castSucc ≫
        SimplexCategory.sd.map (SimplexCategory.σ h) =
    SimplexCategory.sd.map (SimplexCategory.σ h.succ) ≫ subdivisionDegeneracyAt n k ≫
      subdivisionCutAt (SimplexCategory.mk n) k := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact congrFun (finiteChainDegeneracy_rear n k h hkh) (s.obj i)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
