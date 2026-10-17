module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorRightNaturality

/-! # 任意の主導来kernel作用の結合coherence

## 概要
公開作用合成比較と主導来kernel結合子の二経路を任意kernelで同定する。

## 方針
最初の二kernelを右相対K-flat代表で計算し、両経路の自然性により代表同型を消去する。

## 規約と注意
局所Hom条件はD・Eのみ。最後のkernelにK-flat性や列の射影性を追加しない。

## 使われ方
U16a受入と、U16dの実際のPerf制限への結合coherenceの移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]
  (hD : localHomKFlat A D) (hE : localHomKFlat A E)

/-- 最初のkernelの同型に沿って、公開結合二経路の一致を運ぶ。 -/
lemma kernelAssociatorPaths_eq_of_first_iso {P P' : Kernel A D E} (e : P ≅ P')
    (Q : Kernel A E F) (R : Kernel A F G)
    (h : kernelAssociatorLeftPath A D E F G hD P Q R =
      kernelAssociatorRightPath A D E F G hD hE P Q R) :
    kernelAssociatorLeftPath A D E F G hD P' Q R =
      kernelAssociatorRightPath A D E F G hD hE P' Q R := by
  let s := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight ((kernelDerivedTensorFunctor A D E).mapIso e)
      (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R)
  apply (cancel_epi s.hom).1
  change whiskerRight (whiskerRight ((kernelDerivedTensorFunctor A D E).map e.hom)
      (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R) ≫ _ =
    whiskerRight (whiskerRight ((kernelDerivedTensorFunctor A D E).map e.hom)
      (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R) ≫ _
  exact (kernelAssociatorLeftPath_first_naturality A D E F G hD e.hom Q R).trans
    ((congrArg (fun k => k ≫ _) h).trans
      (kernelAssociatorRightPath_first_naturality A D E F G hD hE e.hom Q R).symm)

/-- 二番目のkernelの同型に沿って、公開結合二経路の一致を運ぶ。 -/
lemma kernelAssociatorPaths_eq_of_second_iso (P : Kernel A D E)
    {Q Q' : Kernel A E F} (e : Q ≅ Q') (R : Kernel A F G)
    (h : kernelAssociatorLeftPath A D E F G hD P Q R =
      kernelAssociatorRightPath A D E F G hD hE P Q R) :
    kernelAssociatorLeftPath A D E F G hD P Q' R =
      kernelAssociatorRightPath A D E F G hD hE P Q' R := by
  let s := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (kernelDerivedTensor A D E P)
      ((kernelDerivedTensorFunctor A E F).mapIso e)) (kernelDerivedTensor A F G R)
  apply (cancel_epi s.hom).1
  change whiskerRight (whiskerLeft (kernelDerivedTensor A D E P)
      ((kernelDerivedTensorFunctor A E F).map e.hom)) (kernelDerivedTensor A F G R) ≫ _ =
    whiskerRight (whiskerLeft (kernelDerivedTensor A D E P)
      ((kernelDerivedTensorFunctor A E F).map e.hom)) (kernelDerivedTensor A F G R) ≫ _
  exact (kernelAssociatorLeftPath_second_naturality A D E F G hD P e.hom R).trans
    ((congrArg (fun k => k ≫ _) h).trans
      (kernelAssociatorRightPath_second_naturality A D E F G hD hE P e.hom R).symm)

/-- 任意の主導来kernelで、実際の作用の結合図式の二経路は一致する。 -/
theorem kernelCompositionIso_associator (P : Kernel A D E)
    (Q : Kernel A E F) (R : Kernel A F G) :
    kernelAssociatorLeftPath A D E F G hD P Q R =
      kernelAssociatorRightPath A D E F G hD hE P Q R := by
  obtain ⟨P₀, ⟨eP⟩⟩ := exists_rightKFlat_derived_iso A E D hD P
  obtain ⟨Q₀, ⟨eQ⟩⟩ := exists_rightKFlat_derived_iso A F E hE Q
  obtain ⟨⟨R₀⟩⟩ := R
  apply kernelAssociatorPaths_eq_of_second_iso A D E F G hD hE P eQ
  apply kernelAssociatorPaths_eq_of_first_iso A D E F G hD hE eP
  exact kernelCompositionIso_associator_model A D E F G hD hE P₀ Q₀ R₀

end SerrePositivity.DifferentialGraded.Morita
