module

public import SerrePositivity.KST.Descent.PullbackAction
public import SerrePositivity.KST.Descent.DescentNaturality
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 同変な Cartesian モデルと指定引き戻しの比較

## 概要
二射影が同変な Cartesian モデルの作用を、実際の指定引き戻しの作用と比較する。

## 方針
標準比較同型の同変性を二射影で検査し、指定降下比較をその同型で移す。

## 規約
作用を共役として新しく定義せず、構成済みの pullbackAction との一致を証明する。

## 使われ方
論文 補題 3.2 のテンソル積モデルを実際の Čech の底変換へ接続する。
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] {P X Y B : C} {G : Type*} [Group G]
variable {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} [HasPullback f g]
variable (square : IsPullback p q f g)
variable (actionP : G →* Aut P) (actionX : G →* Aut X)
  (actionY : G →* Aut Y) (actionB : G →* Aut B)
variable (equivariant_f : ∀ a, (actionX a).asIso.hom ≫ f = f ≫ (actionB a).asIso.hom)
  (equivariant_g : ∀ a, (actionY a).asIso.hom ≫ g = g ≫ (actionB a).asIso.hom)
  (equivariant_p : ∀ a, (actionP a).asIso.hom ≫ p = p ≫ (actionX a).asIso.hom)
  (equivariant_q : ∀ a, (actionP a).asIso.hom ≫ q = q ≫ (actionY a).asIso.hom)

include equivariant_p equivariant_q

/-- 概要：Cartesian モデルから指定引き戻しへの標準同型は同変（論文 補題 3.2）。
方針：二射影との合成を計算し、引き戻しの普遍性で比較する。
規約：元の二射影と四頂点の指定作用を保持する。
使われ方：テンソル積モデルと実際の Čech 底変換の作用の比較。 -/
theorem isPullback_isoPullback_equivariant (a : G) :
    (actionP a).asIso.hom ≫ square.isoPullback.hom =
      square.isoPullback.hom ≫
        (pullbackAction f g actionX actionY actionB equivariant_f equivariant_g a).asIso.hom := by
  apply pullback.hom_ext
  · calc
      ((actionP a).asIso.hom ≫ square.isoPullback.hom) ≫ pullback.fst f g =
          (actionP a).asIso.hom ≫ p :=
        (Category.assoc _ _ _).trans
          (congrArg ((actionP a).asIso.hom ≫ ·) square.isoPullback_hom_fst)
      _ = p ≫ (actionX a).asIso.hom := equivariant_p a
      _ = (square.isoPullback.hom ≫
          (pullbackAction f g actionX actionY actionB equivariant_f equivariant_g a).asIso.hom) ≫
          pullback.fst f g := by
        exact ((Category.assoc _ _ _).trans
          ((congrArg (square.isoPullback.hom ≫ ·)
            (pullbackAction_fst f g actionX actionY actionB equivariant_f equivariant_g a)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ (actionX a).asIso.hom) square.isoPullback_hom_fst)))).symm
  · calc
      ((actionP a).asIso.hom ≫ square.isoPullback.hom) ≫ pullback.snd f g =
          (actionP a).asIso.hom ≫ q :=
        (Category.assoc _ _ _).trans
          (congrArg ((actionP a).asIso.hom ≫ ·) square.isoPullback_hom_snd)
      _ = q ≫ (actionY a).asIso.hom := equivariant_q a
      _ = (square.isoPullback.hom ≫
          (pullbackAction f g actionX actionY actionB equivariant_f equivariant_g a).asIso.hom) ≫
          pullback.snd f g := by
        exact ((Category.assoc _ _ _).trans
          ((congrArg (square.isoPullback.hom ≫ ·)
            (pullbackAction_snd f g actionX actionY actionB equivariant_f equivariant_g a)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ (actionY a).asIso.hom) square.isoPullback_hom_snd)))).symm

omit equivariant_p equivariant_q

section TrivialBase

variable {X Y Y' B : C} (f : X ⟶ B) (k : Y ⟶ B) (k' : Y' ⟶ B)
  [HasPullback f k] [HasPullback f k'] (a : G →* Aut X)
  (ha : ∀ s, (a s).asIso.hom ≫ f = f) (j : Y ⟶ Y') (hj : j ≫ k' = k)

/-- 概要：基底変更の射と、元の始域だけの作用は可換（論文 補題 3.2）。
方針：二つの pullback.map の合成公式を両順序に適用する。
規約：基底変更側と共通基底の作用は自明。
使われ方：実際の Čech 各段の射の同変性。 -/
theorem pullbackAction_map_trivialBase (s : G) :
    (pullbackAction f k a 1 1
      (fun s ↦ (ha s).trans (Category.comp_id f).symm)
      (fun _ ↦ (Category.id_comp k).trans (Category.comp_id k).symm) s).asIso.hom ≫
        pullback.map f k f k' (𝟙 X) j (𝟙 B)
          (by simp) ((Category.comp_id k).trans hj.symm) =
      pullback.map f k f k' (𝟙 X) j (𝟙 B)
        (by simp) ((Category.comp_id k).trans hj.symm) ≫
        (pullbackAction f k' a 1 1
          (fun s ↦ (ha s).trans (Category.comp_id f).symm)
          (fun _ ↦ (Category.id_comp k').trans (Category.comp_id k').symm) s).asIso.hom := by
  change pullback.map f k f k (a s).asIso.hom (𝟙 Y) (𝟙 B)
      ((Category.comp_id f).trans (ha s).symm)
      ((Category.comp_id k).trans (Category.id_comp k).symm) ≫ _ =
    _ ≫ pullback.map f k' f k' (a s).asIso.hom (𝟙 Y') (𝟙 B)
      ((Category.comp_id f).trans (ha s).symm)
      ((Category.comp_id k').trans (Category.id_comp k').symm)
  rw [pullback.map_comp, pullback.map_comp]
  simp only [Category.comp_id, Category.id_comp]

end TrivialBase

end SerrePositivity.KST.Descent
