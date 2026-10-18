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
  (I J : MorphismProperty SSet.{u}) [ModelGeneration.CofibrantlyGenerated.{u} I J]
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

end SerrePositivity.KST.Descent.CofibrantCechWeight
