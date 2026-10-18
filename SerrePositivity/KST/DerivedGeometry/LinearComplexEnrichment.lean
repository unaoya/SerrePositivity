module

public import SerrePositivity.KST.DerivedGeometry.LinearComplexMapping

/-!
# 線形加法圏の複体の dg 豊穣

概要：写像複体の合成の単位・結合則を証明し、既存 DGCategory に束ねる。
方針：既存テンソル複体の三重斉次成分で比較する。
規約：通常の複体の Category instance は変更しない。
使われ方：KST D4・§13 決定11、Toën Derived Azumaya §3.2 の層の dg 模型。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

variable {A : Type u} [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

/--
概要：複体の恒等射を写像複体の閉次数零の単位として表す。
方針：既存の unitFromCycle に恒等コチェインを渡す。
規約：任意の非有界複体を扱う。
使われ方：KST D4、Toën §3.2 の dg 圏の単位。
-/
def identity (X : CochainComplex C ℤ) :
    𝟙_ (Complex A) ⟶ mappingComplex A X X :=
  unitFromCycle _ ⟨Cochain.ofHom (𝟙 X), δ_ofHom _⟩

/--
概要：豊穣順の写像複体の合成は結合的。
方針：三重の純斉次テンソルへ帰着し Cochain.comp の結合則と符号を比較する。
規約：符号は pq + pr + qr の二つの展開で一致する。
使われ方：KST D4、Toën §3.2 の層複体の dg 圏。
-/
lemma forwardComposition_assoc (W X Y Z : CochainComplex C ℤ) :
    forwardComposition W X Y ▷ mappingComplex A Y Z ≫ forwardComposition W Y Z =
    (α_ _ _ _).hom ≫ mappingComplex A W X ◁ forwardComposition X Y Z ≫
      forwardComposition W X Z := by
  apply triple_ext
  intro p q r n hn
  simp only [HomologicalComplex.comp_f]
  rw [ι_whiskerRight_assoc, ι_associator_assoc, ι_whiskerLeft_assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro f g h
  change (forwardComposition W Y Z).f n
      (ιTensorObj (mappingComplex A W Y) (mappingComplex A Y Z) (p + q) r n hn
        ((forwardComposition W X Y).f (p + q)
          (ιTensorObj (mappingComplex A W X) (mappingComplex A X Y) p q (p + q) rfl
            (f ⊗ₜ[A] g)) ⊗ₜ[A] h)) =
    (forwardComposition W X Z).f n
      (ιTensorObj (mappingComplex A W X) (mappingComplex A X Z) p (q + r) n (by omega)
        (f ⊗ₜ[A] (forwardComposition X Y Z).f (q + r)
          (ιTensorObj (mappingComplex A X Y) (mappingComplex A Y Z) q r (q + r) rfl
            (g ⊗ₜ[A] h))))
  rw [forwardComposition_apply, forwardComposition_apply]
  rw [forwardComposition_apply, forwardComposition_apply]
  simp only [Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul,
    ← Int.negOnePow_add]
  rw [Cochain.comp_assoc _ _ _ rfl rfl hn]
  congr 1
  congr 1
  ring

/--
概要：恒等コチェインから作る単位は左単位則を満たす。
方針：テンソル単位の成分を評価し、合成の純テンソル式を使う。
規約：豊穣順の単位則として述べる。
使われ方：KST D4、Toën §3.2 の dg 圏の構成。
-/
lemma identity_comp (X Y : CochainComplex C ℤ) :
    (λ_ (mappingComplex A X Y)).inv ≫ identity X ▷ _ ≫
      forwardComposition X X Y = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (leftUnitor' (mappingComplex A X Y)).inv n ≫
    (identity X ▷ mappingComplex A X Y).f n ≫ (forwardComposition X X Y).f n = 𝟙 _
  rw [leftUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerRight_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (forwardComposition X X Y).f n
    (ιTensorObj (mappingComplex A X X) (mappingComplex A X Y) 0 n n (zero_add n)
      ((identity X).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1) ⊗ₜ[A] f)) = f
  rw [forwardComposition_apply]
  change (0 * n).negOnePow •
    (cycleFromUnit _ (identity X)).val.comp f (zero_add n) = f
  rw [identity, cycleFromUnit_unitFromCycle]
  simp

/--
概要：恒等コチェインから作る単位は右単位則を満たす。
方針：右単位同型の成分とコチェインの右単位を比較する。
規約：非有界な写像複体でも同じ式を使う。
使われ方：KST D4、Toën §3.2 の dg 圏の構成。
-/
lemma comp_identity (X Y : CochainComplex C ℤ) :
    (ρ_ (mappingComplex A X Y)).inv ≫ _ ◁ identity Y ≫
      forwardComposition X Y Y = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (rightUnitor' (mappingComplex A X Y)).inv n ≫
    (mappingComplex A X Y ◁ identity Y).f n ≫ (forwardComposition X Y Y).f n = 𝟙 _
  rw [rightUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerLeft_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (forwardComposition X Y Y).f n
    (ιTensorObj (mappingComplex A X Y) (mappingComplex A Y Y) n 0 n (add_zero n)
      (f ⊗ₜ[A] (identity Y).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1))) = f
  rw [forwardComposition_apply]
  change (n * 0).negOnePow •
    f.comp (cycleFromUnit _ (identity Y)).val (add_zero n) = f
  rw [identity, cycleFromUnit_unitFromCycle]
  simp

/--
概要：任意の線形加法圏の複体を既存の DGCategory として豊穣する。
方針：実際の写像複体・単位・合成と証明済みの三法則を束ねる。
規約：汎用の大域 instance とせず、層の圏で明示的に選ぶ。
使われ方：KST D4・§13 決定11、Toën §3.2 の層複体の dg 増強。
-/
@[instance_reducible]
def enrichment : DGCategory A (CochainComplex C ℤ) where
  Hom := mappingComplex A
  id := identity
  comp := forwardComposition
  id_comp := identity_comp
  comp_id := comp_identity
  assoc W X Y Z := by rw [forwardComposition_assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.DerivedGeometry.LinearComplex
