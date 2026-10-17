module
public import SerrePositivity.DifferentialGraded.Resolution.CellComposition
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation

/-! # cell反復列の極限Homの左右単位則

## 概要
cell反復列の極限Homの左右単位則。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma candidateComposition_left_unit (x y : D) :
    (λ_ (candidateHom A D x y)).inv ≫ candidateUnit A D x ▷ candidateHom A D x y ≫
      candidateComposition A D x x y = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  apply chain_ext_apply
  intro k a
  change (candidateComposition A D x x y).f k
    ((candidateUnit A D x ▷ candidateHom A D x y).f k
      ((λ_ (candidateHom A D x y)).inv.f k ((stageInclusion A D n x y).f k a))) =
    (stageInclusion A D n x y).f k a
  rw [← candidateUnit_stage A D n x, complexLeftUnitor_inv_apply, whiskerRight_apply,
    chain_comp_apply, candidateComposition_apply_stage]
  have h := congrArg (fun f : stageHom A D n x y ⟶ stageHom A D n x y => f.f k a)
    ((stage A D n).category.id_comp x y)
  change ((stage A D n).category.comp x x y).f k
    (((stage A D n).category.id x ▷ stageHom A D n x y).f k
      ((λ_ (stageHom A D n x y)).inv.f k a)) = a at h
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply] at h
  exact congrArg ((stageInclusion A D n x y).f k) h

lemma candidateComposition_right_unit (x y : D) :
    (ρ_ (candidateHom A D x y)).inv ≫ candidateHom A D x y ◁ candidateUnit A D y ≫
      candidateComposition A D x y y = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  apply chain_ext_apply
  intro k a
  change (candidateComposition A D x y y).f k
    ((candidateHom A D x y ◁ candidateUnit A D y).f k
      ((ρ_ (candidateHom A D x y)).inv.f k ((stageInclusion A D n x y).f k a))) =
    (stageInclusion A D n x y).f k a
  rw [← candidateUnit_stage A D n y, complexRightUnitor_inv_apply, whiskerLeft_apply,
    chain_comp_apply, candidateComposition_apply_stage]
  have h := congrArg (fun f : stageHom A D n x y ⟶ stageHom A D n x y => f.f k a)
    ((stage A D n).category.comp_id x y)
  change ((stage A D n).category.comp x y y).f k
    ((stageHom A D n x y ◁ (stage A D n).category.id y).f k
      ((ρ_ (stageHom A D n x y)).inv.f k a)) = a at h
  rw [complexRightUnitor_inv_apply, whiskerLeft_apply] at h
  exact congrArg ((stageInclusion A D n x y).f k) h

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
