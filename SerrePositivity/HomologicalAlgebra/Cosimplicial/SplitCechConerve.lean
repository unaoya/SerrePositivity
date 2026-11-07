module

public import Mathlib.AlgebraicTopology.CechNerve
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Homotopy

/-!
# 切断付き Čech 余脈体のホモトピー

## 概要
基底上の二つの自己射が誘導する Čech 余脈体の自己射を余単体ホモトピーで結ぶ。

## 方針
各頂点の挿入に二つの自己射の一方を合成する。切り替えの添字を単体圏の面と退化に沿って追う。

## 規約
基底の構造射はすべての次数で固定する。

## 使われ方
切断付き Čech 余脈体のテンソル後の収縮。
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

variable {C : Type*} [Category* C]
variable (f : Arrow C)
variable [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]

/-- 基底を固定する自己射が誘導する Čech 余脈体の自己射。 -/
def cechEnd (u : f.right ⟶ f.right) (hu : f.hom ≫ u = f.hom) : f.cechConerve ⟶ f.cechConerve :=
  Arrow.mapCechConerve (Arrow.homMk (𝟙 _) u (by simpa using hu.symm))

variable (u v : f.right ⟶ f.right) (hu : f.hom ≫ u = f.hom) (hv : f.hom ≫ v = f.hom)

set_option backward.isDefEq.respectTransparency false in
/-- 二つの自己射を頂点の順に切り替える Čech 余脈体の射。 -/
def cechPrism {n : ℕ} (i : Fin (n + 1)) : f.cechConerve.obj ⦋n + 1⦌ ⟶ f.cechConerve.obj ⦋n⦌ :=
  WidePushout.desc (WidePushout.head _)
    (fun j : Fin (n + 2) =>
      (if j ≤ i.castSucc then u else v) ≫
        WidePushout.ι (fun _ : Fin (n + 1) => f.hom) (i.predAbove j))
    (fun j => by
      split_ifs
      · rw [← Category.assoc, hu]
        exact WidePushout.arrow_ι (arrows := fun _ : Fin (n + 1) => f.hom) (i.predAbove j)
      · rw [← Category.assoc, hv]
        exact WidePushout.arrow_ι (arrows := fun _ : Fin (n + 1) => f.hom) (i.predAbove j))

private theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  by_cases h : i.val < p.val
  · rw [Fin.succAbove_of_castSucc_lt p i h, ite_eq_left h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc p i (Nat.le_of_not_gt h), ite_eq_right h]
    rfl

private theorem val_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (p.predAbove i).val = if p.val < i.val then i.val - 1 else i.val := by
  by_cases h : p.val < i.val
  · rw [Fin.predAbove_of_castSucc_lt p i h, ite_eq_left h]
    rfl
  · rw [Fin.predAbove_of_le_castSucc p i (Nat.le_of_not_gt h), ite_eq_right h]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- 概要：基底上の二つの自己射の Čech 余脈体への作用を結ぶホモトピー。
方針：挿入との合成を計算して余単体ホモトピーの恒等式を示す。
規約：切り替えの頂点までは第一の射を使う。
使われ方：切断付き Čech 余脈体の収縮。 -/
def cechEndHomotopy : CosimplicialHomotopy (cechEnd f u hu) (cechEnd f v hv) where
  h i := (cechPrism f u v hu hv i).op
  h_zero_comp_δ_zero n := by
    apply Quiver.Hom.unop_inj
    apply WidePushout.hom_ext
    · intro k
      simp [cechPrism, cechEnd, SimplicialObject.δ, SimplexCategory.δ]
    · simp [cechPrism, cechEnd, SimplicialObject.δ]
  h_last_comp_δ_last n := by
    apply Quiver.Hom.unop_inj
    apply WidePushout.hom_ext
    · intro k
      simp [cechPrism, cechEnd, SimplicialObject.δ, SimplexCategory.δ, Fin.le_last]
    · simp [cechPrism, cechEnd, SimplicialObject.δ]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply Quiver.Hom.unop_inj
    apply WidePushout.hom_ext
    · intro k
      simp [cechPrism, SimplicialObject.δ, SimplexCategory.δ]
      simp only [Fin.le_def, Fin.val_castSucc] at hij
      congr 1
      · apply if_congr _ rfl rfl
        simp only [Fin.le_def, val_succAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
      · congr 1
        apply Fin.ext
        simp only [val_succAbove, val_predAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
    · simp [cechPrism, SimplicialObject.δ]
  h_succ_comp_δ_castSucc_succ j := by
    apply Quiver.Hom.unop_inj
    apply WidePushout.hom_ext
    · intro k
      simp [cechPrism, SimplicialObject.δ, SimplexCategory.δ]
      congr 1
      · apply if_congr _ rfl rfl
        simp only [Fin.le_def, val_succAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
      · congr 1
        apply Fin.ext
        simp only [val_succAbove, val_predAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
    · simp [cechPrism, SimplicialObject.δ]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply Quiver.Hom.unop_inj
    apply WidePushout.hom_ext
    · intro k
      simp [cechPrism, SimplicialObject.δ, SimplexCategory.δ]
      simp only [Fin.lt_def, Fin.val_castSucc] at hji
      congr 1
      · apply if_congr _ rfl rfl
        simp only [Fin.le_def, val_succAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
      · congr 1
        apply Fin.ext
        simp only [val_succAbove, val_predAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
    · simp [cechPrism, SimplicialObject.δ]
  h_comp_σ_castSucc_of_le i j hij := by
    apply Quiver.Hom.unop_inj
    apply WidePushout.hom_ext
    · intro k
      simp [cechPrism, SimplicialObject.σ, SimplexCategory.σ]
      simp only [Fin.le_def] at hij
      congr 1
      · apply if_congr _ rfl rfl
        simp only [Fin.le_def, val_predAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
      · congr 1
        apply Fin.ext
        simp only [val_predAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
    · simp [cechPrism, SimplicialObject.σ]
  h_comp_σ_succ_of_lt i j hji := by
    apply Quiver.Hom.unop_inj
    apply WidePushout.hom_ext
    · intro k
      simp [cechPrism, SimplicialObject.σ, SimplexCategory.σ]
      simp only [Fin.le_def] at hji
      congr 1
      · apply if_congr _ rfl rfl
        simp only [Fin.le_def, val_predAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
      · congr 1
        apply Fin.ext
        simp only [val_predAbove, Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | omega
    · simp [cechPrism, SimplicialObject.σ]

section Split

variable (r : f.right ⟶ f.left) (hr : f.hom ≫ r = 𝟙 f.left)

set_option backward.isDefEq.respectTransparency false in
/-- 概要：基底への引き戻しを各 copy に適用した Čech 余脈体の退縮。
方針：各 copy に同じ左逆を用いて余積から降ろす。
規約：右辺は基底の定数余単体対象。
使われ方：切断付き Čech 余脈体の収縮。 -/
def cechRetraction : f.cechConerve ⟶ (Functor.const SimplexCategory).obj f.left where
  app n := WidePushout.desc (𝟙 _) (fun _ : Fin (n.len + 1) => r) (fun _ => hr)
  naturality {m n} θ := by
    apply WidePushout.hom_ext
    · intro j
      simp
    · simp

@[simp]
theorem cechAugmentation_retraction :
    f.augmentedCechConerve.hom ≫ cechRetraction f r hr = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  change WidePushout.head _ ≫ (cechRetraction f r hr).app n = 𝟙 f.left
  exact WidePushout.head_desc ..

set_option backward.isDefEq.respectTransparency false in
/-- 概要：切断付き Čech 余脈体の恒等射は、基底に戻る射と余単体ホモトピック。
方針：各 copy で恒等射と左逆・元の射の合成を切り替える。
規約：余増大を戻す向きに退縮を取る。
使われ方：任意の余単体対象との項ごとのテンソル積の比較。 -/
def cechSplitHomotopy : CosimplicialHomotopy (𝟙 f.cechConerve)
    (cechRetraction f r hr ≫ f.augmentedCechConerve.hom) := by
  let e := r ≫ f.hom
  have he : f.hom ≫ e = f.hom := by simp [e, ← Category.assoc, hr]
  have h₁ : cechEnd f (𝟙 _) (Category.comp_id _) = 𝟙 f.cechConerve := by
    apply NatTrans.ext
    funext n
    apply WidePushout.hom_ext
    · intro j
      simp [cechEnd]
      erw [Category.comp_id]
    · simp [cechEnd]
      erw [Category.comp_id]
  have h₂ : cechEnd f e he = cechRetraction f r hr ≫ f.augmentedCechConerve.hom := by
    apply NatTrans.ext
    funext n
    apply WidePushout.hom_ext
    · intro j
      simp [cechEnd, cechRetraction, e]
      exact congrArg (r ≫ ·) (WidePushout.arrow_ι (arrows := fun _ : Fin (n.len + 1) => f.hom) j)
    · simp [cechEnd, cechRetraction]
  rw [← h₁, ← h₂]
  exact cechEndHomotopy f _ _ _ _

/-- 概要：切断付き Čech 余脈体の余増大は、任意の項ごとの二変数関手を施した後も余鎖ホモトピー同値。
方針：第一因子の定値ホモトピーと Čech のホモトピーを組にし、関手を施す。
規約：右因子に Čech 余脈体を置く。
使われ方：結晶比較の Frobenius ひねりと余分な座標の収縮。 -/
def cechSplitCochainEquiv {D E : Type*} [Category* D] [Category* E] [Preadditive E]
    (N : CosimplicialObject D) (F : D × C ⥤ E) :
    HomotopyEquiv
      ((AlgebraicTopology.alternatingCofaceMapComplex E).obj
        (N.prod' ((Functor.const SimplexCategory).obj f.left) ⋙ F))
      ((AlgebraicTopology.alternatingCofaceMapComplex E).obj (N.prod' f.cechConerve ⋙ F)) := by
  let W : CosimplicialObject C ⥤ CosimplicialObject (D × C) := {
    obj X := N.prod' X
    map g := NatTrans.prod' (𝟙 N) g
    map_id X := by
      apply NatTrans.ext
      funext n
      rfl
    map_comp g h := by
      apply NatTrans.ext
      funext n
      apply Prod.ext
      · simp
      · rfl
  }
  let G := W ⋙ (Functor.whiskeringRight SimplexCategory (D × C) E).obj F
  let L := AlgebraicTopology.alternatingCofaceMapComplex E
  let ι : (Functor.const SimplexCategory).obj f.left ⟶ f.cechConerve := f.augmentedCechConerve.hom
  let π := cechRetraction f r hr
  have h : CosimplicialHomotopy (G.map (𝟙 f.cechConerve)) (G.map (π ≫ ι)) :=
    ((CosimplicialHomotopy.refl (𝟙 N)).prod' (cechSplitHomotopy f r hr)).whiskerRight F
  rw [G.map_id, G.map_comp] at h
  refine
    { hom := L.map (G.map ι)
      inv := L.map (G.map π)
      homotopyHomInvId := Homotopy.ofEq ?_
      homotopyInvHomId := ?_ }
  · rw [← L.map_comp, ← G.map_comp, show ι ≫ π = 𝟙 _ from cechAugmentation_retraction f r hr,
      G.map_id]
    exact L.map_id _
  · change Homotopy (L.map (G.map π) ≫ L.map (G.map ι)) (𝟙 (L.obj (G.obj f.cechConerve)))
    rw [← L.map_comp, ← L.map_id]
    exact h.toCochainHomotopy.symm

end Split

end SerrePositivity.Cosimplicial
