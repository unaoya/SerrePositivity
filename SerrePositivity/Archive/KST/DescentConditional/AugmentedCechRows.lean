module

public import SerrePositivity.Archive.KST.DescentConditional.CechWeightAugmentationFubini
public import SerrePositivity.Archive.KST.DescentConditional.AugmentedDerivedCechFubini

/-!
# 増強つき二重 Čech の行ごとの指定比較

## 概要
二重図式の指定増強から各行の増強つき図式の関手を構成し、各行の指定比較を外側の図式へまとめる。

## 方針
curry の自然性を comma 圏の射の可換式に使い、既存の指定増強の自然変換を各行へ適用する。

## 規約
増強元を固定する各行の射を実際に構成する。各行の比較の自然性を追加仮定にしない。

## 使われ方
論文 補題 3.2・3.3 の各方向の降下を反復計算へ貼り合わせる段階。
-/

@[expose] public section

noncomputable section

universe u v w t vH uH vD uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K L : Type u) [SmallCategory K] [SmallCategory L]

/-- 概要：指定された二重増強から各行の増強つき図式の関手（補題 3.2）。
方針：curry した増強を各行で評価し、外側の射の左辺を恒等射にする。
規約：全ての外側の射に自然な実際の関手。使われ方：各行の降下比較の束ね。 -/
def augmentedCechRows (A : AugmentedCechDiagram (K × L)) : K ⥤ AugmentedCechDiagram L where
  obj k := {
    left := A.left
    right := (Functor.curry.obj A.right).obj k
    hom := (Functor.curry.map A.hom).app k }
  map {k l} f := {
    left := 𝟙 A.left
    right := (Functor.curry.obj A.right).map f
    w := (Functor.curry.map A.hom).naturality f }
  map_id k := by
    apply Comma.hom_ext
    · rfl
    · exact (Functor.curry.obj A.right).map_id k
  map_comp f g := by
    apply Comma.hom_ext
    · exact (Category.id_comp _).symm
    · exact (Functor.curry.obj A.right).map_comp f g

/-- 概要：各行の指定重みつき比較を外側で自然に束ねる（補題 3.2）。
方針：構成した行の関手に既存の指定比較を前合成する。
規約：外側の自然性を追加仮定にしない。使われ方：外側の増強つき図式。 -/
abbrev rowWeightedCechAugmentation (V : L ⥤ SSet.{u})
    (r : V ⟶ (Functor.const L).obj (𝟙_ SSet.{u})) (A : AugmentedCechDiagram (K × L)) :
    (Functor.const K).obj A.left ⟶ Functor.curry.obj A.right ⋙ WeightedCones.coneSpace L V :=
  Functor.whiskerLeft (augmentedCechRows K L A) (weightedCechAugmentation L V r)

/-- 概要：各行の指定比較を増強とする外側の図式（補題 3.2）。
方針：元の増強元と、内側の錐空間の列を保持する。
規約：各行の指定比較をそのまま使う。使われ方：外側の指定錐比較。 -/
abbrev rowWeightedCechDiagram (V : L ⥤ SSet.{u})
    (r : V ⟶ (Functor.const L).obj (𝟙_ SSet.{u})) (A : AugmentedCechDiagram (K × L)) :
    AugmentedCechDiagram K := {
  left := A.left
  right := Functor.curry.obj A.right ⋙ WeightedCones.coneSpace L V
  hom := rowWeightedCechAugmentation K L V r A }

/-- 概要：各行の比較の後に外側の指定比較を取る直接の写像（補題 3.2）。
方針：行の比較を増強とする図式へ外側の重みの指定錐比較を適用する。
規約：反復 Fubini 同型から定義しない。使われ方：各方向の降下の貼り合わせ。 -/
abbrev rowwiseWeightedCechAugmentation (W : K ⥤ SSet.{u}) (V : L ⥤ SSet.{u})
    (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u}))
    (r : V ⟶ (Functor.const L).obj (𝟙_ SSet.{u})) (A : AugmentedCechDiagram (K × L)) :
    A.left ⟶ (iteratedCechConeSpace K L W V).obj A.right :=
  (weightedCechAugmentation K W q).app (rowWeightedCechDiagram K L V r A)

/-- 概要：点ごとに持ち上げた随伴の Hom 対応は各成分の元の Hom 対応（補題 3.2）。
方針：持ち上げた単位の成分と Hom 対応の単位による表示を評価する。
規約：任意の圏の随伴に成立する。使われ方：反復した指定錐の行ごとの表示。 -/
theorem cechWhiskerRight_homEquiv_app
    {C : Type v} [Category.{t} C] {D : Type w} [Category.{t} D]
    {T : C ⥤ D} {R : D ⥤ C} (adj : T ⊣ R)
    (A : K ⥤ C) (B : K ⥤ D) (f : A ⋙ T ⟶ B) (k : K) :
    ((adj.whiskerRight K).homEquiv A B f).app k = adj.homEquiv (A.obj k) (B.obj k) (f.app k) := by
  change ((adj.whiskerRight K).unit.app A).app k ≫ R.map (f.app k) =
    adj.unit.app (A.obj k) ≫ R.map (f.app k)
  rw [Adjunction.whiskerRight_unit_app_app]

/-- 概要：curry/uncurry の指定随伴の対応は各二重成分で元の射を保持（補題 3.2）。
方針：指定同値の単位の恒等成分を評価する。
規約：二重成分での実際の等式。使われ方：反復した随伴対応の行ごとの計算。 -/
theorem cechCurrying_homEquiv_app_app (U : K ⥤ L ⥤ SSet.{u}) (F : K × L ⥤ SSet.{u})
    (f : Functor.uncurry.obj U ⟶ F) (k : K) (l : L) :
    (((Functor.currying (C := K) (D := L) (E := SSet.{u})).toAdjunction.homEquiv
      U F f).app k).app l =
      f.app (k, l) := by
  simp [Adjunction.homEquiv_unit, Functor.currying]

/-- 概要：直接構成した反復重み比較は各行の比較の後の外側比較と一致（補題 3.2）。
方針：合成随伴の Hom 対応を分解し、内側の対応の始域自然性を各行で使う。
規約：Fubini 同型や降下の結論は使わない。使われ方：各方向の降下の反復計算。 -/
theorem iteratedWeightedCechAugmentation_rowwise
    (W : K ⥤ SSet.{u}) (V : L ⥤ SSet.{u})
    (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u}))
    (r : V ⟶ (Functor.const L).obj (𝟙_ SSet.{u})) (A : AugmentedCechDiagram (K × L)) :
    (iteratedWeightedCechAugmentation K L W V q r).app A =
      rowwiseWeightedCechAugmentation K L W V q r A := by
  let f := (iteratedCechTensorAugmentation K L W V q r).app A.left ≫ A.hom
  change (iteratedCechConeAdjunction K L W V).homEquiv A.left A.right f =
    (WeightedCones.adjunction K W).homEquiv A.left _
      ((WeightComparison.tensorComparison K q).app A.left ≫ rowWeightedCechAugmentation K L V r A)
  rw [iteratedCechConeAdjunction, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  apply congrArg ((WeightedCones.adjunction K W).homEquiv A.left
    (Functor.curry.obj A.right ⋙ WeightedCones.coneSpace L V))
  apply NatTrans.ext
  funext k
  rw [cechWhiskerRight_homEquiv_app]
  change (WeightedCones.adjunction L V).homEquiv _ _ _ =
    ((WeightComparison.tensorComparison K q).app A.left).app k ≫
      (WeightedCones.adjunction L V).homEquiv A.left _
        ((WeightComparison.tensorComparison L r).app A.left ≫
          (Functor.curry.map A.hom).app k)
  refine Eq.trans ?_ ((WeightedCones.adjunction L V).homEquiv_naturality_left
    (((WeightComparison.tensorComparison K q).app A.left).app k)
    ((WeightComparison.tensorComparison L r).app A.left ≫ (Functor.curry.map A.hom).app k))
  apply congrArg ((WeightedCones.adjunction L V).homEquiv (A.left ⊗ W.obj k)
    ((Functor.curry.obj A.right).obj k))
  apply NatTrans.ext
  funext l
  rw [cechCurrying_homEquiv_app_app]
  change ((((WeightComparison.tensorComparison K q).app A.left).app k ▷ V.obj l) ≫
      (((WeightComparison.tensorComparison L r).app A.left).app l ≫ 𝟙 A.left)) ≫
        A.hom.app (k, l) =
    (((WeightComparison.tensorComparison K q).app A.left).app k ▷ V.obj l) ≫
      (((WeightComparison.tensorComparison L r).app A.left).app l ≫ A.hom.app (k, l))
  simp only [Category.assoc]
  exact congrArg (fun h ↦
    (((WeightComparison.tensorComparison K q).app A.left).app k ▷ V.obj l) ≫
      ((WeightComparison.tensorComparison L r).app A.left).app l ≫ h)
    (Category.id_comp (A.hom.app (k, l)))

variable [ModelCategory SSet.{u}] (I J : MorphismProperty SSet.{u})
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

/-- 概要：各行の実際の指定ホモトピー極限比較を自然に束ねる（補題 3.2）。
方針：行の関手に既存の指定比較を前合成する。
規約：各行の比較の自然性を仮定しない。使われ方：外側の実際の指定比較の増強。 -/
abbrev rowHomotopyCechAugmentation (A : AugmentedCechDiagram (K × L)) :
    (Functor.const K).obj A.left ⟶ (innerCechHomotopyLimit K L I J).obj A.right :=
  Functor.whiskerLeft (augmentedCechRows K L A) (homotopyCechAugmentation L I J)

/-- 概要：各行の実際の比較を増強とする外側の図式（補題 3.2）。
方針：元の増強元と内側の実際のホモトピー極限の列を使う。
規約：指定比較を保持する。使われ方：外側での実際の降下条件。 -/
abbrev rowHomotopyCechDiagram (A : AugmentedCechDiagram (K × L)) : AugmentedCechDiagram K := {
  left := A.left
  right := (innerCechHomotopyLimit K L I J).obj A.right
  hom := rowHomotopyCechAugmentation K L I J A }

/-- 概要：各行の生の比較は内側の指定置換後に各行の実際の比較になる（補題 3.2）。
方針：既存の指定比較の合成の定義を評価する。
規約：自然変換としての等式。使われ方：外側の増強つき図式の間の指定射。 -/
theorem rowWeightedCechAugmentation_to_homotopy (A : AugmentedCechDiagram (K × L)) :
    rowWeightedCechAugmentation K L (HomotopyCones.weight L I J)
        (HomotopyCones.weightComparison L I J) A ≫
      (innerCechConeComparison K L I J).app A.right = rowHomotopyCechAugmentation K L I J A := rfl

/-- 概要：実際の反復指定比較は各行の実際の比較の後の外側比較と一致（補題 3.2・3.3）。
方針：生の反復比較の行表示と、外側の指定比較の自然性を使う。
規約：各行と外側の置換は独立な既存の構成を使う。
使われ方：各方向の実際の降下条件を Fubini へ渡す。 -/
theorem iteratedHomotopyCechAugmentation_rowwise (A : AugmentedCechDiagram (K × L)) :
    (iteratedHomotopyCechAugmentation K L I J).app A =
      (homotopyCechAugmentation K I J).app (rowHomotopyCechDiagram K L I J A) := by
  let B := rowWeightedCechDiagram K L (HomotopyCones.weight L I J)
    (HomotopyCones.weightComparison L I J) A
  let B' := rowHomotopyCechDiagram K L I J A
  let n := (innerCechConeComparison K L I J).app A.right
  let j : B ⟶ B' := {
    left := 𝟙 A.left
    right := n
    w := (Category.id_comp _).trans (rowWeightedCechAugmentation_to_homotopy K L I J A).symm }
  have hn : 𝟙 A.left ≫ (homotopyCechAugmentation K I J).app B' =
      (homotopyCechAugmentation K I J).app B ≫ (HomotopyCones.functor K I J).map n :=
    (homotopyCechAugmentation K I J).naturality j
  change (iteratedWeightedCechAugmentation K L (HomotopyCones.weight K I J)
    (HomotopyCones.weight L I J) (HomotopyCones.weightComparison K I J)
      (HomotopyCones.weightComparison L I J)).app A ≫
    ((HomotopyCones.comparison K I J).app B.right ≫
      (HomotopyCones.functor K I J).map n) = (homotopyCechAugmentation K I J).app B'
  rw [iteratedWeightedCechAugmentation_rowwise]
  exact (Category.assoc
    ((weightedCechAugmentation K (HomotopyCones.weight K I J)
      (HomotopyCones.weightComparison K I J)).app B)
    ((HomotopyCones.comparison K I J).app B.right)
    ((HomotopyCones.functor K I J).map n)).symm.trans (hn.symm.trans (Category.id_comp _))

variable [IsQuillenBifunctor (curriedTensor SSet.{u})]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (Λ : SSet.{u} ⥤ H) [Λ.IsLocalization (weakEquivalences SSet.{u})]
  (Q : (K × L ⥤ SSet.{u}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise (K × L) (weakEquivalences SSet.{u}))]

include hcof Λ Q in
/-- 概要：積添字の実際の降下は各行の比較を増強とする外側の実際の降下と同値（補題 3.2・3.3）。
方針：指定増強を保つ導来 Fubini と実際の反復比較の行表示を合成する。
規約：各行の比較は直接構成した既存の指定比較。使われ方：各方向の降下の貼り合わせ。 -/
theorem cechSpaceDescent_rowwise_iff (A : AugmentedCechDiagram (K × L)) :
    HasCechSpaceDescent (K × L) I J A ↔
      HasCechSpaceDescent K I J (rowHomotopyCechDiagram K L I J A) := by
  rw [cechSpaceDescent_fubini_iff K L I J hcof Λ Q A,
    iteratedHomotopyCechAugmentation_rowwise K L I J A]
  rfl

end SerrePositivity.KST.Descent
