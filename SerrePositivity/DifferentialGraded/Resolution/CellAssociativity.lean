module
public import SerrePositivity.DifferentialGraded.Resolution.CellUnits
public import SerrePositivity.DifferentialGraded.Complexes.TensorCompositionAssociativity

/-! # cell反復列の極限Homの結合則

## 概要
cell反復列の極限Homの結合則。

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

lemma stageComposition_assoc (n : ℕ) (x y z t : D) :
    ((stage A D n).category.comp x y z ▷ stageHom A D n z t) ≫
      (stage A D n).category.comp x z t =
    (α_ (stageHom A D n x y) (stageHom A D n y z) (stageHom A D n z t)).hom ≫
      stageHom A D n x y ◁ (stage A D n).category.comp y z t ≫
        (stage A D n).category.comp x y t := by
  let : DGCategory A D := (stage A D n).category
  exact (e_assoc' (Complex A) x y z t).symm

def candidateTripleIsColimit (x y z t : D) :
    IsColimit (((colimit.cocone (homDiagram A D x y)).tensor
      (colimit.cocone (homDiagram A D y z))).tensor
        (colimit.cocone (homDiagram A D z t))) := by
  letI : IsSifted ℕ := IsFiltered.isSifted
  exact (candidateTensorIsColimit A D x y z).tensor (colimit.isColimit (homDiagram A D z t))

lemma candidateComposition_assoc (x y z t : D) :
    (candidateComposition A D x y z ▷ candidateHom A D z t) ≫ candidateComposition A D x z t =
    (α_ (candidateHom A D x y) (candidateHom A D y z) (candidateHom A D z t)).hom ≫
      candidateHom A D x y ◁ candidateComposition A D y z t ≫ candidateComposition A D x y t := by
  apply (candidateTripleIsColimit A D x y z t).hom_ext
  intro n
  apply HomologicalComplex.Hom.ext
  funext k
  apply SerrePositivity.cochainTensorTriple_hom_ext
    (stageHom A D n x y) (stageHom A D n y z) (stageHom A D n z t) k
  intro p q r hk
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro a b c
  change (candidateComposition A D x z t).f k
    ((candidateComposition A D x y z ▷ candidateHom A D z t).f k
      (((stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ⊗ₘ
          stageInclusion A D n z t).f k
        (ιTensorObj (stageHom A D n x y ⊗ stageHom A D n y z) (stageHom A D n z t)
          (p + q) r k hk
          (ιTensorObj (stageHom A D n x y) (stageHom A D n y z) p q (p + q) rfl
            (a ⊗ₜ[A] b) ⊗ₜ[A] c)))) =
    (candidateComposition A D x y t).f k
      ((candidateHom A D x y ◁ candidateComposition A D y z t).f k
        ((α_ (candidateHom A D x y) (candidateHom A D y z) (candidateHom A D z t)).hom.f k
          (((stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ⊗ₘ
              stageInclusion A D n z t).f k
            (ιTensorObj (stageHom A D n x y ⊗ stageHom A D n y z) (stageHom A D n z t)
              (p + q) r k hk
              (ιTensorObj (stageHom A D n x y) (stageHom A D n y z) p q (p + q) rfl
                (a ⊗ₜ[A] b) ⊗ₜ[A] c)))))
  simp only [tensorMap_apply, whiskerRight_apply, whiskerLeft_apply, associator_apply,
    candidateComposition_apply_stage]
  exact congrArg ((stageInclusion A D n x t).f k)
    (tensorComposition_assoc_apply
      (stageHom A D n x y) (stageHom A D n y z) (stageHom A D n z t)
      (stageHom A D n x z) (stageHom A D n y t) (stageHom A D n x t)
      ((stage A D n).category.comp x y z) ((stage A D n).category.comp x z t)
      ((stage A D n).category.comp y z t) ((stage A D n).category.comp x y t)
      (stageComposition_assoc A D n x y z t) p q r k hk a b c)

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
