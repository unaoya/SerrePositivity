module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorMain
public import SerrePositivity.DifferentialGraded.Morita.CoherenceUnitMain

/-! # 主導来kernel作用の左単位coherence

## 概要
恒等kernelを後に作用させる公開合成比較と主導来左単位子の整合性を証明する。

## 方針
kernel三角図式と作用結合図式を恒等kernel二個に適用し、既存右単位図式へ帰着する。
恒等kernelの作用は恒等関手に同型なので、その後合成を打ち消せる。

## 規約と注意
局所Hom条件はD・Eに明示する。一般の分解変更coherenceは使用しない。

## 使われ方
U16aの両単位・結合整合性の最後の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (hD : localHomKFlat A D) (hE : localHomKFlat A E)

/-- 恒等kernel二個を含む主導来三角図式。 -/
lemma kernelAssociatorIso_identity_triangle (P : Kernel A D E) :
    (kernelAssociatorIso A D E E E hD hE P (kernelIdentity A E) (kernelIdentity A E)).hom ≫
      (((derivedBimoduleComposeFunctor A E E D hD).map
        ((derivedBimoduleLeftUnitIso A E D hD).hom.app P)).app (kernelIdentity A E)) =
    ((derivedBimoduleComposeFunctor A E E D hD).obj P).map
      ((derivedBimoduleRightUnitIso A E E hE).hom.app (kernelIdentity A E)) := by
  exact NatTrans.congr_app (derivedBimoduleTriangle_app A E E D hE hD P) (kernelIdentity A E)

include hE in
/-- 後に恒等kernelを作用させる公開合成比較は、主導来左単位子と整合する。 -/
theorem kernelCompositionIso_leftUnit (P : Kernel A D E) :
    (kernelCompositionIso A D E E hD P (kernelIdentity A E)).hom ≫
      (kernelDerivedTensorFunctor A D E).map ((derivedBimoduleLeftUnitIso A E D hD).hom.app P) =
    whiskerLeft (kernelDerivedTensor A D E P) (kernelIdentityIso A E).hom ≫
      (Functor.rightUnitor (kernelDerivedTensor A D E P)).hom := by
  let I := kernelIdentity A E
  let T := kernelDerivedTensor A E E I
  let c := kernelCompositionIso A D E E hD P I
  let l := (derivedBimoduleLeftUnitIso A E D hD).hom.app P
  let j := (kernelDerivedTensorFunctor A D E).map l
  let r := (derivedBimoduleRightUnitIso A E E hE).hom.app I
  let kl := ((derivedBimoduleComposeFunctor A E E D hD).map l).app I
  let kr := ((derivedBimoduleComposeFunctor A E E D hD).obj P).map r
  have ht : (kernelAssociatorIso A D E E E hD hE P I I).hom ≫ kl = kr :=
    kernelAssociatorIso_identity_triangle A D E hD hE P
  have hta : (kernelDerivedTensorFunctor A D E).map
      (kernelAssociatorIso A D E E E hD hE P I I).hom ≫
      (kernelDerivedTensorFunctor A D E).map kl =
      (kernelDerivedTensorFunctor A D E).map kr := by
    rw [← Functor.map_comp, ht]
  have hf := kernelCompositionIso_first_naturality A D E E hD l I
  have hs := kernelCompositionIso_second_naturality A D E E hD P r
  have hr := kernelCompositionIso_rightUnit A E E hE I
  have ha := kernelCompositionIso_associator A D E E E hD hE P I I
  have heq : whiskerRight (c.hom ≫ j) T ≫ c.hom =
      (Functor.associator (kernelDerivedTensor A D E P) T T).hom ≫
        whiskerLeft (kernelDerivedTensor A D E P)
          (whiskerRight (kernelIdentityIso A E).hom T ≫ (Functor.leftUnitor T).hom) ≫ c.hom := by
    calc
      _ = kernelAssociatorLeftPath A D E E E hD P I I ≫
          (kernelDerivedTensorFunctor A D E).map kl := by
        rw [whiskerRight_comp, Category.assoc]
        erw [hf]
        simp only [kernelAssociatorLeftPath, Category.assoc]
        rfl
      _ = kernelAssociatorRightPath A D E E E hD hE P I I ≫
          (kernelDerivedTensorFunctor A D E).map kl := congrArg (fun k => k ≫ _) ha
      _ = (Functor.associator (kernelDerivedTensor A D E P) T T).hom ≫
          whiskerLeft (kernelDerivedTensor A D E P) (kernelCompositionIso A E E E hE I I).hom ≫
          (kernelCompositionIso A D E E hD P (kernelCompose A E E E hE I I)).hom ≫
          (kernelDerivedTensorFunctor A D E).map kr := by
        dsimp only [kernelAssociatorRightPath]
        simp only [Category.assoc]
        rw [hta]
      _ = (Functor.associator (kernelDerivedTensor A D E P) T T).hom ≫
          whiskerLeft (kernelDerivedTensor A D E P) (kernelCompositionIso A E E E hE I I).hom ≫
          whiskerLeft (kernelDerivedTensor A D E P) ((kernelDerivedTensorFunctor A E E).map r) ≫
          c.hom := by
        slice_lhs 3 4 => erw [← hs]
        rfl
      _ = _ := by
        slice_lhs 2 3 => erw [← whiskerLeft_comp]
        erw [hr]
  apply NatTrans.ext
  funext X
  have hx := NatTrans.congr_app heq X
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.leftUnitor_hom_app, Functor.map_comp] at hx
  erw [Category.comp_id, Category.id_comp] at hx
  have hx' := (cancel_mono (c.hom.app X)).1 hx
  let : T.Faithful := Functor.Faithful.of_iso (kernelIdentityIso A E).symm
  rw [← T.map_comp] at hx'
  have hm := T.map_injective hx'
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id]
  exact hm

end SerrePositivity.DifferentialGraded.Morita
