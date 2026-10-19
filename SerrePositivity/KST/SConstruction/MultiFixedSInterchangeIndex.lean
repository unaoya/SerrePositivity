module
public import SerrePositivity.KST.SConstruction.MultiFixedSInterchangeNaturality

/-! # 全多次数の S 交換の固定方向に関する自然性
概要：残りの次数を独立に保ち、固定した S_m の全次数変更と内外交換の可換性を示す。
方針：二方向交換の内側の自然性を、反復の成分の再帰式で帰納する。
規約：元の全多次数交換を保つ。使われ方：全方向を動かす巡回交換の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 残りの全多次数を保つ固定 S_m の次数変更と交換の厳密な可換性。 -/
lemma multiFixedSEndofunctorIso_index {m m' : ℕ} (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) (X : StableModel.{u})
    (θ : Fin (m' + 1) →o Fin (m + 1)) :
    ((multiSEndofunctor r).obj d).map ((sEndofunctorMap θ).app X) ≫
        (multiFixedSEndofunctorIso m' r d).hom.app X =
      (multiFixedSEndofunctorIso m r d).hom.app X ≫
        (sEndofunctorMap θ).app (((multiSEndofunctor r).obj d).obj X) := by
  induction r with
  | zero =>
    rw [multiFixedSEndofunctorIso_zero_app, multiFixedSEndofunctorIso_zero_app]
    change (sEndofunctorMap θ).app X ≫ 𝟙 _ = 𝟙 _ ≫ (sEndofunctorMap θ).app X
    rw [Category.comp_id, Category.id_comp]
  | succ r ih =>
    rw [multiFixedSEndofunctorIso_succ_app, multiFixedSEndofunctorIso_succ_app]
    let F := sEndofunctor (d 0).unop.len
    let D := (multiSEndofunctor r).obj (fun i => d i.succ)
    have hn : F.map ((sEndofunctorMap θ).app (D.obj X)) ≫
        (sInterchangeStableIso (d 0).unop.len m' (D.obj X)).hom =
      (sInterchangeStableIso (d 0).unop.len m (D.obj X)).hom ≫
        (sEndofunctorMap θ).app (F.obj (D.obj X)) :=
      Subtype.ext (sInterchange_innerMap (d 0).unop.len (D.obj X) θ)
    change F.map (D.map ((sEndofunctorMap θ).app X)) ≫
      (F.map ((multiFixedSEndofunctorIso m' r (fun i => d i.succ)).hom.app X) ≫
        (sInterchangeStableIso (d 0).unop.len m' (D.obj X)).hom) =
      (F.map ((multiFixedSEndofunctorIso m r (fun i => d i.succ)).hom.app X) ≫
        (sInterchangeStableIso (d 0).unop.len m (D.obj X)).hom) ≫
          (sEndofunctorMap θ).app (F.obj (D.obj X))
    rw [← Category.assoc, ← F.map_comp, ih, F.map_comp, Category.assoc, hn, Category.assoc]

end SerrePositivity.KST.SConstruction
