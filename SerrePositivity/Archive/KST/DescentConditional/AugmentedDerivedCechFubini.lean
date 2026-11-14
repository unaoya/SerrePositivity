module

public import SerrePositivity.Archive.KST.DescentConditional.CechWeightAugmentationFubini
public import SerrePositivity.Archive.KST.DescentConditional.AugmentedCechWeightChange
public import SerrePositivity.Archive.KST.DescentConditional.DerivedCechFubini

/-!
# 指定増強を保つ実際の導来 Čech Fubini

## 概要
実際の積添字ホモトピー極限と反復ホモトピー極限の構成済み Fubini 同型が指定増強を保つことを示す。

## 方針
重み変更、指定置換、重みつき Fubini、反復置換を順に追跡し、それぞれの可換式を合成する。

## 規約
反復側の増強は二つの指定重み増強と独立な置換比較から直接構成する。
Sp 内の Tot への実現は別に残る。

## 使われ方
論文 補題 3.2・3.3 の指定降下比較と二重 Čech の導来 Fubini。
-/

@[expose] public section

noncomputable section

universe u vH uH vD uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K L : Type u) [SmallCategory K] [SmallCategory L] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

local instance : IsLocallyPresentable.{u} SSet.{u} :=
  WeightedCones.simplicialSet_isLocallyPresentable

/-- 概要：反復した実際のホモトピー極限への直接構成した指定増強（補題 3.2）。
方針：二つの指定重み増強からの錐を、独立な行・外側の指定置換比較で送る。
規約：Fubini 同型から逆算して定義しない。使われ方：指定比較を保つ実際の Fubini。 -/
abbrev iteratedHomotopyCechAugmentation : cechAugmentedSource (K × L) ⟶
    cechAugmentedDiagram (K × L) ⋙ iteratedCechHomotopyLimit K L I J :=
  iteratedWeightedCechAugmentation K L (HomotopyCones.weight K I J) (HomotopyCones.weight L I J)
      (HomotopyCones.weightComparison K I J) (HomotopyCones.weightComparison L I J) ≫
    Functor.whiskerLeft (cechAugmentedDiagram (K × L)) (iteratedCechConeComparison K L I J)

variable [IsQuillenBifunctor (curriedTensor SSet.{u})]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]
  (Q : (K × L ⥤ SSet.{u}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise (K × L) (weakEquivalences SSet.{u}))]
  (constant : H ⥤ D)
  (e : (Functor.const (K × L) : SSet.{u} ⥤ _) ⋙ Q ≅ Λ ⋙ constant)

/-- 概要：構成済みの実際の導来 Fubini は指定増強と全図式で自然に可換（補題 3.2・3.3）。
方針：増強の指定置換への自然性と、重み変更・重みつき Fubini の可換式を合成する。
規約：反復増強は独立に直接構成してあり、同型の存在から増強を定義しない。
使われ方：二重 Čech の指定降下比較の反復計算。 -/
theorem homotopyCechAugmentation_fubini :
    Functor.whiskerRight (homotopyCechAugmentation (K × L) I J) Λ ≫
        Functor.whiskerLeft (cechAugmentedDiagram (K × L))
          (cechHomotopyLimitFubiniIso K L I J Λ hcof Q constant e).hom =
      Functor.whiskerRight (iteratedHomotopyCechAugmentation K L I J) Λ := by
  apply NatTrans.ext
  funext A
  let W := HomotopyCones.weight K I J
  let V := HomotopyCones.weight L I J
  let q := HomotopyCones.weightComparison K I J
  let r := HomotopyCones.weightComparison L I J
  let ρ := (HomotopyCones.replacementComparison (K × L) I J).app A.right
  let B : AugmentedCechDiagram (K × L) := {
    left := A.left
    right := (HomotopyCones.replacement (K × L) I J).obj A.right
    hom := A.hom ≫ ρ }
  let j : A ⟶ B := { left := 𝟙 A.left, right := ρ, w := by simp [B] }
  let aw := weightedCechAugmentation (K × L) (externalCechWeight K L W V)
    (externalCechWeightAugmentation K L q r)
  let ai := iteratedWeightedCechAugmentation K L W V q r
  let E := homotopyCechProductWeightComparisonIso K L I J hcof Λ Q constant e
  let g := weightedCechFubiniIso K L W V
  let n := iteratedCechConeComparison K L I J
  let C := iteratedCechReplacementComparisonIso K L I J Λ
  have hx : (computedWeightedCechAugmentation (K × L) I J (externalCechWeight K L W V)
        (externalCechWeightAugmentation K L q r)).app A = aw.app B := by
    have hn : 𝟙 A.left ≫ aw.app B = aw.app A ≫
        (WeightedCones.coneSpace (K × L) (externalCechWeight K L W V)).map ρ := aw.naturality j
    exact hn.symm.trans (Category.id_comp _)
  have hw : Λ.map ((computedWeightedCechAugmentation (K × L) I J
        (externalCechWeight K L W V) (externalCechWeightAugmentation K L q r)).app A) ≫
        E.hom.app A.right = Λ.map ((homotopyCechAugmentation (K × L) I J).app A) :=
    congrArg (fun b ↦ b.app A)
      (computedWeightedCechAugmentation_weightChange (K × L) I J _
        (homotopyCechProductWeight_isCofibrant K L I J) _
        (homotopyCechProductWeightAugmentation_weakEquivalence K L hcof I J)
        hcof Λ Q constant e)
  have hw' : Λ.map ((homotopyCechAugmentation (K × L) I J).app A) ≫ E.inv.app A.right =
      Λ.map (aw.app B) := by
    calc
      Λ.map ((homotopyCechAugmentation (K × L) I J).app A) ≫ E.inv.app A.right =
          (Λ.map ((computedWeightedCechAugmentation (K × L) I J
            (externalCechWeight K L W V) (externalCechWeightAugmentation K L q r)).app A) ≫
              E.hom.app A.right) ≫ E.inv.app A.right := congrArg (fun b ↦ b ≫ _) hw.symm
      _ = Λ.map ((computedWeightedCechAugmentation (K × L) I J
            (externalCechWeight K L W V) (externalCechWeightAugmentation K L q r)).app A) := by
        rw [Category.assoc, E.hom_inv_id_app]
        exact Category.comp_id _
      _ = Λ.map (aw.app B) := congrArg Λ.map hx
  have hr : aw.app B ≫ g.hom.app B.right = ai.app B :=
    congrArg (fun b ↦ b.app B) (weightedCechAugmentation_fubini K L W V q r)
  have hi : ai.app B ≫ n.app B.right = (iteratedHomotopyCechAugmentation K L I J).app A ≫
      (iteratedCechHomotopyLimit K L I J).map ρ := by
    have hn : 𝟙 A.left ≫ (iteratedHomotopyCechAugmentation K L I J).app B =
        (iteratedHomotopyCechAugmentation K L I J).app A ≫
          (iteratedCechHomotopyLimit K L I J).map ρ :=
      (iteratedHomotopyCechAugmentation K L I J).naturality j
    exact (Category.id_comp _).symm.trans hn
  have hC : C.hom.app A.right = Λ.map ((iteratedCechHomotopyLimit K L I J).map ρ) := rfl
  have hf : (cechHomotopyLimitFubiniIso K L I J Λ hcof Q constant e).hom.app A.right =
      (E.inv.app A.right ≫ Λ.map (g.hom.app B.right)) ≫
        (Λ.map (n.app B.right) ≫ C.inv.app A.right) := rfl
  change Λ.map ((homotopyCechAugmentation (K × L) I J).app A) ≫
    (cechHomotopyLimitFubiniIso K L I J Λ hcof Q constant e).hom.app A.right = _
  rw [hf]
  calc
    Λ.map ((homotopyCechAugmentation (K × L) I J).app A) ≫
        ((E.inv.app A.right ≫ Λ.map (g.hom.app B.right)) ≫
          (Λ.map (n.app B.right) ≫ C.inv.app A.right)) =
      ((Λ.map ((homotopyCechAugmentation (K × L) I J).app A) ≫ E.inv.app A.right) ≫
        Λ.map (g.hom.app B.right)) ≫ Λ.map (n.app B.right) ≫ C.inv.app A.right := by
          simp only [Category.assoc]
    _ = (Λ.map (aw.app B) ≫ Λ.map (g.hom.app B.right)) ≫
        Λ.map (n.app B.right) ≫ C.inv.app A.right := by rw [hw']
    _ = Λ.map (ai.app B) ≫ Λ.map (n.app B.right) ≫ C.inv.app A.right := by
      rw [← Functor.map_comp, hr]
    _ = Λ.map (ai.app B ≫ n.app B.right) ≫ C.inv.app A.right := by
      simp only [Functor.map_comp, Category.assoc]
    _ = Λ.map ((iteratedHomotopyCechAugmentation K L I J).app A ≫
        (iteratedCechHomotopyLimit K L I J).map ρ) ≫ C.inv.app A.right :=
      congrArg (fun b ↦ Λ.map b ≫ _) hi
    _ = (Λ.map ((iteratedHomotopyCechAugmentation K L I J).app A) ≫
        C.hom.app A.right) ≫ C.inv.app A.right := by rw [Functor.map_comp, hC]
    _ = Λ.map ((iteratedHomotopyCechAugmentation K L I J).app A) := by
      rw [Category.assoc, C.hom_inv_id_app]
      exact Category.comp_id _

/-- 概要：内部構成した定数比較を使う実際の Fubini も指定増強を保持（補題 3.2・3.3）。
方針：既存の局所化からの定数関手と指定比較を前の可換式へ適用する。
規約：定数比較の追加の入力は不要。使われ方：指定 Čech 降下の反復計算。 -/
theorem homotopyCechAugmentation_fubiniCanonical :
    Functor.whiskerRight (homotopyCechAugmentation (K × L) I J) Λ ≫
        Functor.whiskerLeft (cechAugmentedDiagram (K × L))
          (cechHomotopyLimitFubiniCanonicalIso K L I J Λ hcof Q).hom =
      Functor.whiskerRight (iteratedHomotopyCechAugmentation K L I J) Λ :=
  homotopyCechAugmentation_fubini K L I J hcof Λ Q
    (HomotopyLimit.localizedConstant (K × L) Λ Q)
    (HomotopyLimit.constantComparison (K × L) Λ Q)

include hcof Λ Q in
/-- 概要：積添字の実際の指定降下は反復した実際の指定比較の弱同値と同値（補題 3.2・3.3）。
方針：指定増強を保つ実際の Fubini と模型の弱同値の飽和性を使う。
規約：指定反復比較は二つの重み増強と独立な置換から直接構成する。
使われ方：二重 Čech の各方向の計算から元の指定降下へ戻す。 -/
theorem cechSpaceDescent_fubini_iff (A : AugmentedCechDiagram (K × L)) :
    HasCechSpaceDescent (K × L) I J A ↔
      weakEquivalences SSet.{u} ((iteratedHomotopyCechAugmentation K L I J).app A) := by
  change weakEquivalences SSet.{u} _ ↔ weakEquivalences SSet.{u} _
  rw [Quillen.weakEquivalences_iff_isIso_map Λ, Quillen.weakEquivalences_iff_isIso_map Λ]
  have h : Λ.map ((homotopyCechAugmentation (K × L) I J).app A) ≫
      (cechHomotopyLimitFubiniCanonicalIso K L I J Λ hcof Q).hom.app A.right =
        Λ.map ((iteratedHomotopyCechAugmentation K L I J).app A) :=
    congrArg (fun b ↦ b.app A) (homotopyCechAugmentation_fubiniCanonical K L I J hcof Λ Q)
  rw [← h]
  exact (isIso_comp_right_iff _ _).symm

end SerrePositivity.KST.Descent
