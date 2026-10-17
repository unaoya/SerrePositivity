module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionFamilies

/-! # K-flat代表による導来kernel合成の両射計算

## 概要
U12e-localの指定K-flat代表での合成計算を、両kernelの射について同じsquareにまとめる。

## 方針
最初のkernelの射の計算と、後のkernelの射への自然性を貼り、通常合成の関手性を使う。

## 規約と注意
必要な局所Hom条件は始域Dだけ。後のkernelは任意の通常代表。

## 使われ方
U16aの自然なkernel合成比較の主局所化への降下で使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 右相対K-flat代表による導来合成の計算は、両kernelの任意射に自然。 -/
lemma kernelComposeKFlatValueIso_naturality (hD : localHomKFlat A D)
    {P P' : RightKFlatBimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    kernelComposeMap A D E F hD ((bimoduleToDerived A E D).map f.hom)
        ((bimoduleToDerived A F E).map g) ≫
        (derivedBimoduleComposeKFlatValueIso A F E D hD P' Q').hom =
      (derivedBimoduleComposeKFlatValueIso A F E D hD P Q).hom ≫
        (bimoduleToDerived A F D).map (composeMap A F E D g f.hom) := by
  have hf := derivedBimoduleComposeKFlatValueIso_naturality A F E D hD f Q
  have hg := (derivedBimoduleComposeKFlatIso A F E D hD P').hom.naturality
    ((bimoduleToDerived A F E).map g)
  rw [derivedComposeWith_map_base] at hg
  change _ ≫ (derivedBimoduleComposeKFlatValueIso A F E D hD P' Q').hom =
    (derivedBimoduleComposeKFlatValueIso A F E D hD P' Q).hom ≫ _ at hg
  dsimp only [kernelComposeMap]
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
  rw [← Functor.map_comp, ← composeMap_comp, Category.id_comp, Category.comp_id]

end SerrePositivity.DifferentialGraded.Morita
