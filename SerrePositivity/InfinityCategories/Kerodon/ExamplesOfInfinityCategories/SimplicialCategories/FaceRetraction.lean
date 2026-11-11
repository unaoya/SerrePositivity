module

public import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
# 面と標準退化の順序計算

概要：coherent nerve のホーンの面から Hom 写像を回収する道具を構成する。
方針：面と退化の順序写像、Path の関手性、共通の端点への型の移送を使う。
規約：面候補の貼合せは HornHollow、ホーン充填は Quasicategory に置く。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT）。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe w v u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {n : ℕ}
/-- 概要：面を除いた順序へ戻す標準の退化写像を定義する。
方針：Mathlib の factor_δ が使う退化写像を選ぶ。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの Hom データの貼合せ。 -/
def faceRetraction (j : Fin (n + 2)) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.σ (Fin.predAbove 0 j)
/-- 概要：面による因子分解の写像は標準退化との合成である。
方針：factor_δ の定義を用いる。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの Hom データの貼合せ。 -/
lemma faceRetraction_factor {m : ℕ} (α : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2)) :
    SimplexCategory.factor_δ α j = α ≫ faceRetraction j := rfl
/-- 概要：除いた頂点以外では退化後の面への埋め込みは恒等になる。
方針：定値単体に factor_δ_spec を適用する。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの Hom データの貼合せ。 -/
lemma faceRetraction_point (j : Fin (n + 2)) (a : Fin (n + 2)) (ha : a ≠ j) :
    j.succAbove ((faceRetraction j).toOrderHom a) = a := by
  have h := congrArg (fun f ↦ f.toOrderHom 0)
    (SimplexCategory.factor_δ_spec (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ a) j (fun _ ↦ ha))
  exact h
/-- 概要：面への埋め込みの後に退化を適用すると元の頂点に戻る。
方針：succAbove の単射性と除外頂点でないことを使う。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの Hom データの貼合せ。 -/
lemma faceRetraction_succAbove (j : Fin (n + 2)) (a : Fin (n + 1)) :
    (faceRetraction j).toOrderHom (j.succAbove a) = a := by
  apply (Fin.strictMono_succAbove j).injective
  exact faceRetraction_point j (j.succAbove a) (Fin.succAbove_ne j a)
/-- 概要：面への埋め込みと標準退化の合成は恒等射になる。
方針：頂点で前の計算を使う。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの Hom データの貼合せ。 -/
lemma faceRetraction_section (j : Fin (n + 2)) :
    SimplexCategory.δ j ≫ faceRetraction j = 𝟙 ⦋n⦌ := by
  ext a : 3
  exact faceRetraction_succAbove j a
/-- 概要：除いた頂点を避ける単体は退化後の面への埋め込みで回収できる。
方針：Mathlib の factor_δ_spec を用いる。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの Hom データの貼合せ。 -/
lemma faceRetraction_spec {m : ℕ} (α : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2))
    (hα : ∀ a, α.toOrderHom a ≠ j) :
    α ≫ faceRetraction j ≫ SimplexCategory.δ j = α :=
  SimplexCategory.factor_δ_spec α j hα
/-- 概要：除いた頂点を含まない部分集合は二つの像で回収できる。
方針：各点に退化と面への埋め込みの逆写像性を使う。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの Hom データの貼合せ。 -/
lemma faceRetraction_image (j : Fin (n + 2)) (S : Set (Fin (n + 2))) (hj : j ∉ S) :
    j.succAbove '' ((faceRetraction j).toOrderHom '' S) = S := by
  rw [← Set.image_comp]
  convert Set.image_id S using 1
  apply Set.image_congr
  intro a ha
  exact faceRetraction_point j a (fun h ↦ hj (h ▸ ha))
/-- 概要：ULift 上でも除いた頂点を避ける部分集合を回収できる。
方針：各点の down に退化と面の逆写像性を使う。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの Hom データの貼合せ。 -/
lemma faceRetraction_ulift_image (j : Fin (n + 2)) (S : Set (ULift.{u} (Fin (n + 2))))
    (hj : ∀ a ∈ S, a.down ≠ j) :
    (SimplexCategory.δ j).toOrderHom.uliftMap ''
      ((faceRetraction j).toOrderHom.uliftMap '' S) = S := by
  rw [← Set.image_comp]
  convert Set.image_id S using 1
  apply Set.image_congr
  intro a ha
  apply ULift.ext
  exact faceRetraction_point j a.down (hj a ha)
/-- 概要：面と退化からの Path の豊穣関手の合成は恒等関手になる。
方針：順序写像の合成の計算を thickening の関手性へ移す。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの Hom データの貼合せ。 -/
lemma thickening_faceRetraction_section (j : Fin (n + 2)) :
    (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).comp SSet
      (SimplicialThickening.functor (faceRetraction j).toOrderHom.uliftMap) =
        EnrichedFunctor.id SSet (SimplicialThickening (ULift.{w} (Fin (n + 1)))) := by
  rw [← SimplicialThickening.functor_comp]
  have h : (faceRetraction j).toOrderHom.uliftMap.comp
      (SimplexCategory.δ j).toOrderHom.uliftMap =
        OrderHom.id (α := ULift.{w} (Fin (n + 1))) := by
    apply OrderHom.ext
    funext x
    apply ULift.ext
    exact faceRetraction_succAbove j x.down
  rw [h, SimplicialThickening.functor_id]


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
