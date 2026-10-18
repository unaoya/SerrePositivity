module

public import SerrePositivity.KST.Descent.Axioms
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# 同変な cospan の引き戻しの作用

## 概要
同変な二射の実際の引き戻しに G 作用を構成し、二射影の同変性を証明する。

## 方針
引き戻しの map を各群元に適用し、逆元による逆写像と群の法則を普遍性で検査する。

## 規約
基底の作用も含み、引き戻しの基底が自明作用であるとは要求しない。
圏の実際の引き戻しに対する補題で、ホモトピー引き戻しを構成したとは主張しない。

## 使われ方
論文 定理 3.1 の中心と例外部分の同変作用。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] {X Y Z : C} {G : Type*} [Group G]
variable (f : X ⟶ Z) (k : Y ⟶ Z) [HasPullback f k]
variable (actionX : G →* Aut X) (actionY : G →* Aut Y) (actionZ : G →* Aut Z)
variable (equivariant_f : ∀ g, (actionX g).asIso.hom ≫ f = f ≫ (actionZ g).asIso.hom)
variable (equivariant_k : ∀ g, (actionY g).asIso.hom ≫ k = k ≫ (actionZ g).asIso.hom)

/-- 概要：同変な cospan の引き戻し上の群元の自己同型（論文 定理 3.1）。
方針：二つの map を g と g⁻¹ から作り、二射影で逆の法則を検査する。
規約：基底を含む三つの指定作用を保持する。
使われ方：引き戻しの G 作用の構成。 -/
noncomputable def pullbackActionIso (g : G) : pullback f k ≅ pullback f k where
  hom := pullback.map f k f k (actionX g).asIso.hom (actionY g).asIso.hom
    (actionZ g).asIso.hom (equivariant_f g).symm (equivariant_k g).symm
  inv := pullback.map f k f k (actionX g⁻¹).asIso.hom (actionY g⁻¹).asIso.hom
    (actionZ g⁻¹).asIso.hom (equivariant_f g⁻¹).symm (equivariant_k g⁻¹).symm
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, map_inv, Aut.inv_asIso,
        Iso.symm_hom, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, map_inv, Aut.inv_asIso,
        Iso.symm_hom, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- 概要：同変な cospan の引き戻し上の G 作用（論文 定理 3.1）。
方針：各群元の自己同型と、引き戻しの普遍性による群の法則を束ねる。
規約：射影の像の作用から一意に決まる作用。
使われ方：軌道正方形の中心と例外部分を実際に同変にする。 -/
noncomputable def pullbackAction : G →* Aut (pullback f k) where
  toFun g := Aut.of (pullbackActionIso f k actionX actionY actionZ equivariant_f equivariant_k g)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply pullback.hom_ext <;>
      simp only [pullbackActionIso, map_one, Aut.one_asIso, Iso.refl_hom,
        pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.id_comp]
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    apply pullback.hom_ext <;>
      simp only [pullbackActionIso, map_mul, Aut.mul_asIso, Iso.trans_hom, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- 概要：引き戻しの第一射影は同変（論文 定理 3.1）。
方針：map の第一射影の合成公式。
規約：X の指定された作用との同変性。
使われ方：軌道正方形の上辺。 -/
@[reassoc] theorem pullbackAction_fst (g : G) :
    (pullbackAction f k actionX actionY actionZ equivariant_f equivariant_k g).asIso.hom ≫
        pullback.fst f k = pullback.fst f k ≫ (actionX g).asIso.hom := by
  exact pullback.lift_fst _ _ _

/-- 概要：引き戻しの第二射影は同変（論文 定理 3.1）。
方針：map の第二射影の合成公式。
規約：Y の指定された作用との同変性。
使われ方：軌道正方形の左辺。 -/
@[reassoc] theorem pullbackAction_snd (g : G) :
    (pullbackAction f k actionX actionY actionZ equivariant_f equivariant_k g).asIso.hom ≫
        pullback.snd f k = pullback.snd f k ≫ (actionY g).asIso.hom := by
  exact pullback.lift_snd _ _ _

end SerrePositivity.KST.Descent
