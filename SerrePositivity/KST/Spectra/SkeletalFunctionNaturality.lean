module

public import SerrePositivity.KST.Spectra.SkeletalCellFiberNaturality
public import SerrePositivity.KST.Spectra.PointedCoproductHomNaturality
public import SerrePositivity.KST.Spectra.SkeletalFiberFunctions

/-!
概要：骨格の fiber のセルごとの関数複体の表示の係数自然性。
方針：セルの cofiber の比較、余積の Hom の座標表示、fiber の比較の自然性を合成する。
規約：点つき同型と通常の係数射による厳密な可換式。
使われ方：Goerss–Jardine VIII §1。高次係数群への自然な移送。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[reassoc]
lemma cellHomFunctionIso_natural (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}}
    (p : Y ⟶ Z) (d : ℕ) :
    PointedObject.basedHomMap (cellCofiber K d) (Y := Y) (Z := Z) p ≫
        (cellHomFunctionIso K Z d).hom =
      (cellHomFunctionIso K Y d).hom ≫ SimplicialFunctionComplex.pointedPost
        (relativeCellComplexOfMono.Cell (K.skeleton d).ι d)
        (PointedObject.basedHomMap (SimplexCell.sphere.{u} d) (Y := Y) (Z := Z) p) := by
  have hs : PointedObject.basedHomMap (cellCofiber K d) (Y := Y) (Z := Z) p ≫
      (MonoidalClosed.pre (cellCoproductIso K d).inv).app Z =
    (MonoidalClosed.pre (cellCoproductIso K d).inv).app Y ≫
      PointedObject.basedHomMap
        (∐ fun (_ : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) ↦
          SimplexCell.sphere.{u} d) (Y := Y) (Z := Z) p :=
    (MonoidalClosed.pre (cellCoproductIso K d).inv).naturality p
  have ht := pointedCoproductHomIso_natural
    (relativeCellComplexOfMono.Cell (K.skeleton d).ι d) (SimplexCell.sphere.{u} d) p
  change _ ≫ ((MonoidalClosed.pre (cellCoproductIso K d).inv).app Z ≫ _) =
    ((MonoidalClosed.pre (cellCoproductIso K d).inv).app Y ≫ _) ≫ _
  erw [← Category.assoc, hs, Category.assoc, ht, ← Category.assoc]

/-- 概要：実際の fiber のセルの Hom の関数表示は係数射に自然。
方針：cell の Hom の関数表示の自然性を、fiber の比較の逆同型と合成する。
規約：Kan 性を要求しない点つき同型の等式。
使われ方：Goerss–Jardine VIII §1。非退化単体ごとの群の自然性。 -/
@[reassoc]
lemma stageFiberFunctionIso_natural (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}}
    (p : Y ⟶ Z) (n : ℕ) :
    UnbasedPointedMapping.stageFiberMap K (Y := Y) (Z := Z) p n ≫
        (stageFiberFunctionIso K Z n).hom =
      (stageFiberFunctionIso K Y n).hom ≫ SimplicialFunctionComplex.pointedPost
        (relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1))
        (PointedObject.basedHomMap (SimplexCell.sphere.{u} (n + 1)) (Y := Y) (Z := Z) p) := by
  have hs := congrArg (fun t ↦ (stageFiberCellIso K Y n).inv ≫ t ≫
      (stageFiberCellIso K Z n).inv) (stageFiberCellIso_natural K p n)
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at hs
  change _ ≫ ((stageFiberCellIso K Z n).inv ≫ (cellHomFunctionIso K Z (n + 1)).hom) =
    ((stageFiberCellIso K Y n).inv ≫ (cellHomFunctionIso K Y (n + 1)).hom) ≫ _
  rw [← Category.assoc, ← hs, Category.assoc, cellHomFunctionIso_natural, ← Category.assoc]

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
