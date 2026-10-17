module
public import SerrePositivity.DifferentialGraded.Morita.KernelAugmentation

/-! # 通常kernel作用の合成と既存bimodule結合子

## 概要
二つの通常kernelの作用を順に行う関手を、合成kernelの通常作用へ比較する。

## 方針
主Homへの射を各出力対象で評価して入れ子表示を同定し、既存の全Hom自然な結合子を使う。

## 規約と注意
各dg圏のSmall.{u}を明示し、通常合成にはlocalHomKFlatを要求しない。
導来化した合成比較の同型性は、別途相対K-flatモデルを用いて証明する。

## 使われ方
U16aのkernelCompositionIsoを、通常結合子と入力の解像度計算へ接続する。
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
  (P : Bimodule A E D) (Q : Bimodule A F E)

/-- 二つのtensor作用の主Hom mapは、既存bimodule合成の入れ子表示のmapに一致する。 -/
lemma kernelTensorComposition_map (M N : RightModule A D) :
    (kernelTensor A D E P).map M N ≫
        (kernelTensor A E F Q).map ((kernelTensor A D E P).obj M)
          ((kernelTensor A D E P).obj N) =
      (BimoduleTensor.compose A F E (RightModule A D) Q
        (BimoduleTensor.compose A E D (RightModule A D) P
          (DGFunctor.id (RightModule A D)))).toFunctor.map M N := by
  apply moduleHom_ext
  intro f
  rw [Category.assoc, kernelTensor_map_π A E F Q]
  exact (compose_leftMap_π A F E (RightModule A D) Q
    (BimoduleTensor.compose A E D (RightModule A D) P (DGFunctor.id (RightModule A D))) M N f).symm

/-- 二つのtensor dg関手の合成と、同じ入れ子bimoduleのdg関手表示は一致する。 -/
lemma kernelTensorComposition_eq :
    (kernelTensor A D E P).comp (kernelTensor A E F Q) =
      (BimoduleTensor.compose A F E (RightModule A D) Q
        (BimoduleTensor.compose A E D (RightModule A D) P
          (DGFunctor.id (RightModule A D)))).toFunctor := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (kernelTensor A D E P).comp (kernelTensor A E F Q))
    (G := (BimoduleTensor.compose A F E (RightModule A D) Q
      (BimoduleTensor.compose A E D (RightModule A D) P
        (DGFunctor.id (RightModule A D)))).toFunctor) (fun _ => rfl)
  intro M N
  change ((kernelTensor A D E P).map M N ≫
    (kernelTensor A E F Q).map _ _) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact kernelTensorComposition_map A D E F P Q M N

/-- 閉零関手の合成を、入れ子bimoduleの閉零関手へ同定する。 -/
def kernelTensorCompositionSourceIso :
    (kernelTensor A D E P).onClosed ⋙ (kernelTensor A E F Q).onClosed ≅
      (BimoduleTensor.compose A F E (RightModule A D) Q
        (BimoduleTensor.compose A E D (RightModule A D) P
          (DGFunctor.id (RightModule A D)))).toFunctor.onClosed :=
  (EnrichedFunctor.forgetComp (kernelTensor A D E P) (kernelTensor A E F Q)).symm ≪≫
    eqToIso (congrArg (fun G : DGFunctor A (RightModule A D) (RightModule A F) => G.onClosed)
      (kernelTensorComposition_eq A D E F P Q))

/-- 入れ子tensorを合成kernelの作用へ送る、既存bimodule結合子の閉零表示。 -/
def kernelTensorAssociatorClosedIso :
    (BimoduleTensor.compose A F E (RightModule A D) Q
        (BimoduleTensor.compose A E D (RightModule A D) P
          (DGFunctor.id (RightModule A D)))).toFunctor.onClosed ≅
      (kernelTensor A D F (BimoduleTensor.compose A F E D Q P)).onClosed :=
  NatIso.ofComponents (fun M =>
    (BimoduleCategory.evaluation A F (RightModule A D) (ForgetEnrichment.to (Complex A) M)).mapIso
      (associatorIso A F E D (RightModule A D) Q P (DGFunctor.id (RightModule A D))).symm)
    (fun f => (kernelClosedFamilyNatTrans A F (RightModule A D)
      (associatorIso A F E D (RightModule A D) Q P
        (DGFunctor.id (RightModule A D))).inv).naturality f)

/-- 通常kernel作用の関手合成は、通常合成kernelの作用と自然同型。 -/
def kernelTensorCompositionClosedIso :
    (kernelTensor A D E P).onClosed ⋙ (kernelTensor A E F Q).onClosed ≅
      (kernelTensor A D F (BimoduleTensor.compose A F E D Q P)).onClosed :=
  kernelTensorCompositionSourceIso A D E F P Q ≪≫
    kernelTensorAssociatorClosedIso A D E F P Q

/-- 通常kernelの合成比較を、入力のH⁰商と出力のH⁰商へ自然に降ろした同型。 -/
def kernelTensorCompositionHomotopyIso :
    (kernelTensor A D E P).onHomotopy ⋙ (kernelTensor A E F Q).onHomotopy ≅
      (kernelTensor A D F (BimoduleTensor.compose A F E D Q P)).onHomotopy :=
  CategoryTheory.Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (kernelTensor A D E P).onHomotopy_fac)
        (kernelTensor A E F Q).onHomotopy ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (kernelTensor A D E P).onClosed
        (eqToIso (kernelTensor A E F Q).onHomotopy_fac) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (kernelTensorCompositionClosedIso A D E F P Q)
        (moduleToHomotopy A F) ≪≫
      (eqToIso (kernelTensor A D F (BimoduleTensor.compose A F E D Q P)).onHomotopy_fac).symm)

end SerrePositivity.DifferentialGraded.Morita
