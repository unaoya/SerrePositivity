module

public import SerrePositivity.KST.Descent.WeightedCechConeCompatibility
public import SerrePositivity.KST.Descent.WeightedCechDerivedComparison

/-!
# 導来した重みつき錐の指定増強との整合性

## 概要
重みの可縮増強を使った導来定数関手の比較が、指定されたテンソルから定数への射を保つことを示す。

## 方針
局所化からの fully faithful な制限の逆像による比較の定義を評価する。

## 規約
比較の存在だけでなく、構成した同型と指定増強の等式を扱う。

## 使われ方
論文 補題 3.2・3.3 の指定 Čech 増強の導来 Fubini への移送。
-/

@[expose] public section

noncomputable section

universe u vH uH vD uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent.CofibrantCechWeight

variable (K : Type u) [SmallCategory K] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{u})]

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

variable (W : K ⥤ SSet.{u})
  (hW : let := Projective.modelCategory K I J; IsCofibrant W)
  (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u}))
  (hq : ∀ k, weakEquivalences SSet.{u} (q.app k))
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]
  (Q : (K ⥤ SSet.{u}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u}))]
  (LF : H ⥤ D) (α : Λ ⋙ LF ⟶ WeightedCones.tensorDiagram K W ⋙ Q)
  [LF.IsLeftDerivedFunctor α (weakEquivalences SSet.{u})]
  (constant : H ⥤ D)
  (e : (Functor.const K : SSet.{u} ⥤ _) ⋙ Q ≅ Λ ⋙ constant)

/-- 概要：構成した導来テンソル同型は指定重み増強と可換（論文 補題 3.2）。
方針：fully faithful な局所化の制限が逆像を元へ戻す公式を使う。
規約：既存の導来比較 α と指定増強 q を保持する。
使われ方：元の錐の指定増強を導来随伴へ渡す。 -/
theorem derivedTensorConstantIso_fac :
    Functor.whiskerLeft Λ (derivedTensorConstantIso K I J W hW q hq hcof Λ Q LF α constant e).hom =
      α ≫ Functor.whiskerRight (WeightComparison.tensorComparison K q) Q ≫ e.hom := by
  exact (Localization.fullyFaithfulWhiskeringLeft Λ (weakEquivalences SSet.{u}) D).map_preimage _

/-- 概要：導来テンソル同型の逆も指定増強と可換（論文 補題 3.2）。
方針：順方向の可換式を単位同型の可逆性で反転する。
規約：逆比較でも同じ α と q を用いる。使われ方：指定増強の随伴像の比較。 -/
theorem derivedTensorConstantIso_inv_fac (X : SSet.{u}) :
    (derivedTensorConstantIso K I J W hW q hq hcof Λ Q LF α constant e).inv.app (Λ.obj X) ≫
        (α.app X ≫ Q.map ((WeightComparison.tensorComparison K q).app X)) = e.inv.app X := by
  let d := derivedTensorConstantIso K I J W hW q hq hcof Λ Q LF α constant e
  have hd : d.hom.app (Λ.obj X) =
      α.app X ≫ Q.map ((WeightComparison.tensorComparison K q).app X) ≫ e.hom.app X :=
    congrArg (fun a ↦ a.app X)
      (derivedTensorConstantIso_fac K I J W hW q hq hcof Λ Q LF α constant e)
  apply (cancel_mono (e.hom.app X)).mp
  calc
    (d.inv.app (Λ.obj X) ≫
        (α.app X ≫ Q.map ((WeightComparison.tensorComparison K q).app X))) ≫ e.hom.app X =
        d.inv.app (Λ.obj X) ≫ d.hom.app (Λ.obj X) := by rw [Category.assoc, Category.assoc, ← hd]
    _ = 𝟙 _ := d.inv_hom_id_app (Λ.obj X)
    _ = e.inv.app X ≫ e.hom.app X := (e.inv_hom_id_app X).symm

variable (RF : D ⥤ H) (β : WeightedCones.coneSpace K W ⋙ Λ ⟶ Q ⋙ RF)
  [RF.IsRightDerivedFunctor β (Projective.objectwise K (weakEquivalences SSet.{u}))]

/-- 概要：導来定数随伴の錐の像は、指定重み増強による元の錐の導来像に一致（補題 3.2）。
方針：導来定数比較の可換式と実際の Quillen 随伴の導来 Hom の計算式を合成する。
規約：指定された増強 a と q を保ち、抽象的な同型の存在だけで置き換えない。
使われ方：Čech の指定増強を Fubini と分裂降下の計算へ移す。 -/
theorem derivedConstantAdjunction_augmentation_mate (X : SSet.{u}) (F : K ⥤ SSet.{u})
    (a : (Functor.const K).obj X ⟶ F) :
    (derivedConstantAdjunction K I J W hW q hq hcof Λ Q LF α constant e RF β).homEquiv
        (Λ.obj X) (Q.obj F) (e.inv.app X ≫ Q.map a) =
      Λ.map ((WeightedCones.adjunction K W).homEquiv X F
        ((WeightComparison.tensorComparison K q).app X ≫ a)) ≫ β.app F := by
  let d := derivedTensorConstantIso K I J W hW q hq hcof Λ Q LF α constant e
  have hd : d.hom.app (Λ.obj X) =
      α.app X ≫ Q.map ((WeightComparison.tensorComparison K q).app X) ≫ e.hom.app X :=
    congrArg (fun b ↦ b.app X)
      (derivedTensorConstantIso_fac K I J W hW q hq hcof Λ Q LF α constant e)
  have hp : d.hom.app (Λ.obj X) ≫ (e.inv.app X ≫ Q.map a) =
      α.app X ≫ Q.map ((WeightComparison.tensorComparison K q).app X ≫ a) := by
    rw [hd, Functor.map_comp]
    simp [Category.assoc]
  let := Projective.modelCategory K I J
  have := WeightedCones.tensorDiagram_isLeftQuillen K I J W hW
  have := WeightedCones.coneSpace_isRightQuillen K I J W hW
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u})))
  have : RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (RF.IsRightDerivedFunctor β
      (Projective.objectwise K (weakEquivalences SSet.{u})))
  change ((Quillen.derivedAdjunction Λ Q
    (WeightedCones.adjunction K W) α β).ofNatIsoLeft d).homEquiv
    (Λ.obj X) (Q.obj F) (e.inv.app X ≫ Q.map a) = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, hp]
  exact Quillen.derivedAdjunction_homEquiv Λ Q (WeightedCones.adjunction K W) α β X F _

/-- 概要：指定重みの錐空間から指定置換後の計算への比較（論文 補題 3.2）。
方針：既存の置換比較を同じ錐関手で写す。
規約：任意の同型へ交換しない。使われ方：元の錐の導来像との可換式。 -/
abbrev weightedComparison : WeightedCones.coneSpace K W ⟶ weightedFunctor K I J W :=
  Functor.whiskerRight (HomotopyCones.replacementComparison K I J) (WeightedCones.coneSpace K W)

/-- 概要：実際の計算同型は元の指定右導来比較を保持（論文 補題 3.2）。
方針：置換比較に関する β の自然性と、構成した計算同型の逆像の式を使う。
規約：fibrant でない元の図式も含む。使われ方：指定増強の相関した導来計算。 -/
theorem computesDerivedIso_fac :
    Functor.whiskerRight (weightedComparison K I J W) Λ ≫
        (computesDerivedIso K I J W hW Q Λ RF β).hom = β := by
  let := Projective.modelCategory K I J
  have := WeightedCones.coneSpace_isRightQuillen K I J W hW
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u})))
  have : RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (RF.IsRightDerivedFunctor β
      (Projective.objectwise K (weakEquivalences SSet.{u})))
  let r := HomotopyCones.replacement K I J
  let c := HomotopyCones.replacementComparison K I J
  let a := Functor.whiskerLeft r β
  let b := Functor.whiskerRight c (Q ⋙ RF)
  have : ∀ F, IsIso (a.app F) := by
    intro F
    have := HomotopyCones.replacement_isFibrant K I J F
    exact Quillen.rightComparison_isIso Λ Q β (r.obj F)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  have : ∀ F, IsIso (b.app F) := by
    intro F
    have : IsIso (Q.map (c.app F)) := Localization.inverts Q
      (weakEquivalences (K ⥤ SSet.{u})) _
      (HomotopyCones.replacementComparison_weakEquivalence K I J F)
    change IsIso (RF.map (Q.map (c.app F)))
    infer_instance
  have : IsIso b := NatIso.isIso_of_isIso_app b
  have hc : (computesDerivedIso K I J W hW Q Λ RF β).hom ≫ b = a := by
    change (asIso a ≪≫ (asIso b).symm).hom ≫ b = a
    simp
  apply (cancel_mono b).mp
  rw [Category.assoc, hc]
  apply NatTrans.ext
  funext F
  exact β.naturality (c.app F)

/-- 概要：相関した随伴の指定増強の像は実際の計算同型と可換（論文 補題 3.2）。
方針：同じ β を使う導来随伴の Hom の式と、実際の計算同型の可換式を合成する。
規約：随伴と計算同型を別々に選ばない。使われ方：指定増強を保持する重み変更。 -/
theorem DerivedData.augmentation_mate (d : DerivedData K W Λ Q)
    (X : SSet.{u}) (F : K ⥤ SSet.{u}) (a : (Functor.const K).obj X ⟶ F) :
    (DerivedData.constantAdjunction K I J W hW q hq hcof Λ Q constant e d).homEquiv
        (Λ.obj X) (Q.obj F) (e.inv.app X ≫ Q.map a) =
      Λ.map ((WeightedCones.adjunction K W).homEquiv X F
        ((WeightComparison.tensorComparison K q).app X ≫ a) ≫
          (weightedComparison K I J W).app F) ≫
        (DerivedData.computationIso K I J W hW Λ Q d).hom.app F := by
  let := d.leftDerived
  let := d.rightDerived
  have hd := derivedConstantAdjunction_augmentation_mate K I J W hW q hq hcof Λ Q
    d.leftFunctor d.leftComparison constant e d.rightFunctor d.rightComparison X F a
  have hc : Λ.map ((weightedComparison K I J W).app F) ≫
      (DerivedData.computationIso K I J W hW Λ Q d).hom.app F = d.rightComparison.app F :=
    congrArg (fun b ↦ b.app F)
      (computesDerivedIso_fac K I J W hW Λ Q d.rightFunctor d.rightComparison)
  rw [Functor.map_comp, Category.assoc, hc]
  exact hd

/-- 概要：構成した重み変更の同型そのものが指定増強の像を保持（論文 補題 3.2）。
方針：相関した二つの導来データの増強計算と、右随伴同型の随伴像の保持を合成する。
規約：元の増強 a と二つの指定重み増強を固定する。
使われ方：既存の実際のホモトピー極限への指定 Čech 比較の移送。 -/
theorem comparisonIso_augmentation (X : SSet.{u}) (F : K ⥤ SSet.{u})
    (a : (Functor.const K).obj X ⟶ F) :
    Λ.map ((WeightedCones.adjunction K W).homEquiv X F
        ((WeightComparison.tensorComparison K q).app X ≫ a) ≫
          (weightedComparison K I J W).app F) ≫
        (comparisonIso K I J W hW q hq hcof Λ Q constant e).hom.app F =
      Λ.map ((WeightedCones.adjunction K (HomotopyCones.weight K I J)).homEquiv X F
        ((WeightComparison.tensorComparison K (HomotopyCones.weightComparison K I J)).app X ≫ a) ≫
          (HomotopyCones.comparison K I J).app F) := by
  let dw := derivedData K I J W hW Λ Q
  let dc := derivedData K I J (HomotopyCones.weight K I J)
    (HomotopyCones.weight_isCofibrant K I J) Λ Q
  let aw := DerivedData.constantAdjunction K I J W hW q hq hcof Λ Q constant e dw
  let ac := DerivedData.constantAdjunction K I J (HomotopyCones.weight K I J)
    (HomotopyCones.weight_isCofibrant K I J) (HomotopyCones.weightComparison K I J)
    (HomotopyCones.weightComparison_objectwiseWeakEquivalence K I J) hcof Λ Q constant e dc
  let iw := DerivedData.computationIso K I J W hW Λ Q dw
  let ic := DerivedData.computationIso K I J (HomotopyCones.weight K I J)
    (HomotopyCones.weight_isCofibrant K I J) Λ Q dc
  have hw : aw.homEquiv (Λ.obj X) (Q.obj F) (e.inv.app X ≫ Q.map a) =
      Λ.map ((WeightedCones.adjunction K W).homEquiv X F
        ((WeightComparison.tensorComparison K q).app X ≫ a) ≫
          (weightedComparison K I J W).app F) ≫ iw.hom.app F :=
    DerivedData.augmentation_mate K I J W hW q hq hcof Λ Q constant e dw X F a
  have hc : ac.homEquiv (Λ.obj X) (Q.obj F) (e.inv.app X ≫ Q.map a) =
      Λ.map ((WeightedCones.adjunction K (HomotopyCones.weight K I J)).homEquiv X F
        ((WeightComparison.tensorComparison K (HomotopyCones.weightComparison K I J)).app X ≫ a) ≫
          (HomotopyCones.comparison K I J).app F) ≫ ic.hom.app F :=
    DerivedData.augmentation_mate K I J (HomotopyCones.weight K I J)
      (HomotopyCones.weight_isCofibrant K I J) (HomotopyCones.weightComparison K I J)
      (HomotopyCones.weightComparison_objectwiseWeakEquivalence K I J) hcof Λ Q constant e dc X F a
  have hi : (comparisonIso K I J W hW q hq hcof Λ Q constant e).hom.app F =
      iw.hom.app F ≫ (aw.rightAdjointUniq ac).hom.app (Q.obj F) ≫ ic.inv.app F := rfl
  apply (cancel_mono (ic.hom.app F)).mp
  rw [hi]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Category.assoc, ← hw, ← hc]
  have hunit : (aw.rightAdjointUniq ac).hom.app (Q.obj F) ≫
      𝟙 ((Q ⋙ dc.rightFunctor).obj F) = (aw.rightAdjointUniq ac).hom.app (Q.obj F) :=
    Category.comp_id _
  exact (congrArg (fun k ↦ aw.homEquiv (Λ.obj X) (Q.obj F)
    (e.inv.app X ≫ Q.map a) ≫ k) hunit).trans
      (cechConeMate_rightAdjointUniq aw ac (e.inv.app X ≫ Q.map a))

end SerrePositivity.KST.Descent.CofibrantCechWeight
