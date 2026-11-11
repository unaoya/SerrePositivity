module

public import SerrePositivity.KST.Descent.WeightedCechAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.DerivedConstantAdjunction

/-!
# 可縮な cofibrant 重みによる実際のホモトピー極限の計算

## 概要
任意の cofibrant な可縮重みの錐空間を fibrant 置換後に取ると、定数関手の導来右随伴を計算する。

## 方針
重みとのテンソルの左 Quillen 性と単位重みへの弱同値を導来し、実際の随伴を導来する。

## 規約
通常の図式の極限を使わない。単体集合の模型での右導来関手の比較であり、Sp 内の Tot への接続は別工程。

## 使われ方
論文 補題 3.2・3.3 の二重 Čech の外重みと既存のホモトピー錐の重みの比較。
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

/-- 概要：指定 fibrant 置換後の実際の重みつき錐空間（論文 補題 3.2）。
方針：既存の射影的 fibrant 置換と、実際の右随伴を合成する。
規約：重みの cofibrancy は導来性の証明で使う。使われ方：ホモトピー極限の模型。 -/
abbrev weightedFunctor : (K ⥤ SSet.{u}) ⥤ SSet.{u} :=
  HomotopyCones.replacement K I J ⋙ WeightedCones.coneSpace K W

/-- 概要：指定重みの錐空間は実際の右導来関手を計算（論文 補題 3.2）。
方針：fibrant 対象での導来比較と実際の置換の弱同値を局所化する。
規約：任意に供給された右導来関手と自然同型で比較する。
使われ方：異なる cofibrant 重みの計算の同定。 -/
def computesDerivedIso {D : Type uD} [Category.{vD} D] {H : Type uH} [Category.{vH} H]
    (Q : (K ⥤ SSet.{u}) ⥤ D)
    [Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u}))]
    (L : SSet.{u} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{u})] (RF : D ⥤ H)
    (β : WeightedCones.coneSpace K W ⋙ L ⟶ Q ⋙ RF)
    [RF.IsRightDerivedFunctor β (Projective.objectwise K (weakEquivalences SSet.{u}))] :
    weightedFunctor K I J W ⋙ L ≅ Q ⋙ RF := by
  let := Projective.modelCategory K I J
  have := WeightedCones.coneSpace_isRightQuillen K I J W hW
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u})))
  have : RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (RF.IsRightDerivedFunctor β
      (Projective.objectwise K (weakEquivalences SSet.{u})))
  let a : weightedFunctor K I J W ⋙ L ⟶ HomotopyCones.replacement K I J ⋙ Q ⋙ RF :=
    Functor.whiskerLeft (HomotopyCones.replacement K I J) β
  let b : Q ⋙ RF ⟶ HomotopyCones.replacement K I J ⋙ Q ⋙ RF :=
    Functor.whiskerRight (HomotopyCones.replacementComparison K I J) (Q ⋙ RF)
  have : ∀ F, IsIso (a.app F) := by
    intro F
    have := HomotopyCones.replacement_isFibrant K I J F
    exact Quillen.rightComparison_isIso L Q β ((HomotopyCones.replacement K I J).obj F)
  have : ∀ F, IsIso (b.app F) := by
    intro F
    have : IsIso (Q.map ((HomotopyCones.replacementComparison K I J).app F)) :=
      Localization.inverts Q (weakEquivalences (K ⥤ SSet.{u})) _
        (HomotopyCones.replacementComparison_weakEquivalence K I J F)
    change IsIso (RF.map (Q.map ((HomotopyCones.replacementComparison K I J).app F)))
    infer_instance
  have : IsIso a := NatIso.isIso_of_isIso_app a
  have : IsIso b := NatIso.isIso_of_isIso_app b
  let ea := asIso a
  let eb := asIso b
  exact ea ≪≫ eb.symm


variable (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{u}))
  (hq : ∀ k, weakEquivalences SSet.{u} (q.app k))
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)

variable {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (L : SSet.{u} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{u})]
  (Q : (K ⥤ SSet.{u}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u}))]
  (LF : H ⥤ D)
  (α : L ⋙ LF ⟶ WeightedCones.tensorDiagram K W ⋙ Q)
  [LF.IsLeftDerivedFunctor α (weakEquivalences SSet.{u})]
  (constant : H ⥤ D) (e : (Functor.const K : SSet.{u} ⥤ _) ⋙ Q ≅ L ⋙ constant)


/-- 概要：実際の重みのテンソルから定数への弱同値を導来する（論文 補題 3.2）。
方針：全 cofibrancy と局所化の普遍性を使う。
規約：指定増強を用いる。使われ方：右導来錐関手の随伴の同定。 -/
def derivedTensorConstantIso : LF ≅ constant := by
  let := Projective.modelCategory K I J
  have := WeightedCones.tensorDiagram_isLeftQuillen K I J _ hW
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u})))
  have : ∀ X, IsIso (α.app X) := by
    intro X
    have := WeightComparison.all_cofibrant hcof X
    exact Quillen.leftComparison_isIso L Q α X
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let c := WeightComparison.tensorComparison K q
  let b : WeightedCones.tensorDiagram K W ⋙ Q ⟶
      (Functor.const K : SSet.{u} ⥤ _) ⋙ Q := Functor.whiskerRight c Q
  have : ∀ X, IsIso (b.app X) := by
    intro X
    change IsIso (Q.map (c.app X))
    exact Localization.inverts Q (weakEquivalences (K ⥤ SSet.{u})) _
      (WeightComparison.tensorComparison_weakEquivalence K hcof
        q hq X)
  have : IsIso b := NatIso.isIso_of_isIso_app b
  let ea := asIso α
  let eb := asIso b
  exact (Localization.fullyFaithfulWhiskeringLeft L (weakEquivalences SSet.{u}) D).preimageIso
    (ea ≪≫ eb ≪≫ e)

/-- 概要：重みつき右導来錐関手は導来定数関手の右随伴（論文 補題 3.2）。
方針：実際の Quillen 随伴を導来し、左随伴の比較を移す。
規約：右随伴性を追加仮定にしない。使われ方：ホモトピー極限の比較。 -/
def derivedConstantAdjunction (RF : D ⥤ H)
    (β : WeightedCones.coneSpace K W ⋙ L ⟶ Q ⋙ RF)
    [RF.IsRightDerivedFunctor β (Projective.objectwise K (weakEquivalences SSet.{u}))] :
    constant ⊣ RF := by
  let := Projective.modelCategory K I J
  have := WeightedCones.tensorDiagram_isLeftQuillen K I J _ hW
  have := WeightedCones.coneSpace_isRightQuillen K I J W hW
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u})))
  have : RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (RF.IsRightDerivedFunctor β
      (Projective.objectwise K (weakEquivalences SSet.{u})))
  let adj := Quillen.derivedAdjunction L Q (WeightedCones.adjunction K W) α β
  exact adj.ofNatIsoLeft (derivedTensorConstantIso K I J W hW q hq hcof L Q LF α constant e)

include hW q hq hcof e in
/-- 概要：指定可縮重みの計算を与える導来右随伴は実際に存在する（論文 補題 3.2）。
方針：構成済みの導来関手を取り、随伴性と計算の比較を証明する。
規約：導来関手の存在を新しい入力にしない。使われ方：重みを変更する自然同型。 -/
lemma exists_rightAdjoint_constant :
    ∃ RF : D ⥤ H, Nonempty (constant ⊣ RF) ∧
      Nonempty (weightedFunctor K I J W ⋙ L ≅ Q ⋙ RF) := by
  let := Projective.modelCategory K I J
  have := WeightedCones.tensorDiagram_isLeftQuillen K I J _ hW
  have := WeightedCones.coneSpace_isRightQuillen K I J W hW
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u})))
  let T := WeightedCones.tensorDiagram K W ⋙ Q
  let R := WeightedCones.coneSpace K W ⋙ L
  let LF := T.totalLeftDerived L (weakEquivalences SSet.{u})
  let α := T.totalLeftDerivedCounit L (weakEquivalences SSet.{u})
  let RF := R.totalRightDerived Q (weakEquivalences (K ⥤ SSet.{u}))
  let β := R.totalRightDerivedUnit Q (weakEquivalences (K ⥤ SSet.{u}))
  have : RF.IsRightDerivedFunctor β
      (Projective.objectwise K (weakEquivalences SSet.{u})) :=
    inferInstanceAs (RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ SSet.{u})))
  exact ⟨RF, ⟨derivedConstantAdjunction K I J W hW q hq hcof L Q LF α constant e RF β⟩,
    ⟨computesDerivedIso K I J W hW Q L RF β⟩⟩


/-- 概要：同じ比較射から随伴と計算同型を構成する導来データ（論文 補題 3.2）。
方針：左右の導来関手とその指定比較・導来性を同時に保持する。
規約：後で実際に構成するデータであり、新しい存在の仮定ではない。
使われ方：随伴と計算同型の選択を分離せず、指定増強との整合性を追跡する。 -/
structure DerivedData where
  /-- 概要：左導来関手（補題 3.2）。方針：テンソルを導来する。
  規約：比較と一緒に保持。使われ方：導来定数随伴。 -/
  leftFunctor : H ⥤ D
  /-- 概要：左の指定導来比較（補題 3.2）。方針：元のテンソルへの射を保持する。
  規約：任意の同型へ置換しない。使われ方：増強との可換式。 -/
  leftComparison : L ⋙ leftFunctor ⟶ WeightedCones.tensorDiagram K W ⋙ Q
  /-- 概要：指定左比較の導来性（補題 3.2）。方針：実際の導来関手の普遍性。
  規約：構成から供給する。使われ方：導来随伴。 -/
  leftDerived : leftFunctor.IsLeftDerivedFunctor leftComparison (weakEquivalences SSet.{u})
  /-- 概要：右導来関手（補題 3.2）。方針：錐関手を導来する。
  規約：比較と一緒に保持。使われ方：ホモトピー極限の計算。 -/
  rightFunctor : D ⥤ H
  /-- 概要：右の指定導来比較（補題 3.2）。方針：元の錐空間からの射を保持する。
  規約：同じ射を随伴と計算に使う。使われ方：増強の随伴像。 -/
  rightComparison : WeightedCones.coneSpace K W ⋙ L ⟶ Q ⋙ rightFunctor
  /-- 概要：指定右比較の導来性（補題 3.2）。方針：実際の導来関手の普遍性。
  規約：構成から供給する。使われ方：計算同型と随伴の両方。 -/
  rightDerived : rightFunctor.IsRightDerivedFunctor rightComparison
    (Projective.objectwise K (weakEquivalences SSet.{u}))

/-- 概要：相関した左右の導来データを実際に構成（論文 補題 3.2）。
方針：既存の totalLeftDerived・totalRightDerived とその指定比較を使う。
規約：存在証明の独立な選択を用いない。使われ方：増強を保つ重み変更。 -/
def derivedData : DerivedData K W L Q := by
  let := Projective.modelCategory K I J
  have := WeightedCones.tensorDiagram_isLeftQuillen K I J W hW
  have := WeightedCones.coneSpace_isRightQuillen K I J W hW
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{u})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{u})))
  let T := WeightedCones.tensorDiagram K W ⋙ Q
  let R := WeightedCones.coneSpace K W ⋙ L
  exact {
    leftFunctor := T.totalLeftDerived L (weakEquivalences SSet.{u})
    leftComparison := T.totalLeftDerivedCounit L (weakEquivalences SSet.{u})
    leftDerived := inferInstance
    rightFunctor := R.totalRightDerived Q (weakEquivalences (K ⥤ SSet.{u}))
    rightComparison := R.totalRightDerivedUnit Q (weakEquivalences (K ⥤ SSet.{u}))
    rightDerived := inferInstanceAs
      ((R.totalRightDerived Q (weakEquivalences (K ⥤ SSet.{u}))).IsRightDerivedFunctor
        (R.totalRightDerivedUnit Q (weakEquivalences (K ⥤ SSet.{u})))
        (weakEquivalences (K ⥤ SSet.{u}))) }

/-- 概要：相関した指定比較から導来定数随伴を構成（論文 補題 3.2）。
方針：左右の同じ比較に実際の導来随伴の構成を適用する。
規約：随伴を独立に選ばない。使われ方：指定増強の計算との整合性。 -/
def DerivedData.constantAdjunction (d : DerivedData K W L Q) : constant ⊣ d.rightFunctor := by
  letI := d.leftDerived
  letI := d.rightDerived
  exact derivedConstantAdjunction K I J W hW q hq hcof L Q d.leftFunctor d.leftComparison
    constant e d.rightFunctor d.rightComparison

/-- 概要：同じ右導来比較から計算同型を構成（論文 補題 3.2）。
方針：指定比較を fibrant 置換で評価する。
規約：上の随伴と同じ β を使う。使われ方：元の錐との可換式。 -/
def DerivedData.computationIso (d : DerivedData K W L Q) :
    weightedFunctor K I J W ⋙ L ≅ Q ⋙ d.rightFunctor := by
  letI := d.rightDerived
  exact computesDerivedIso K I J W hW Q L d.rightFunctor d.rightComparison

/-- 概要：可縮な cofibrant 重みの計算は既存の実際のホモトピー極限と自然同型（補題 3.2）。
方針：同じ指定導来比較から随伴と計算を構成し、右随伴の一意性で比較する。
規約：単体集合と図式の弱同値での局所化後の自然同型であり、通常の極限ではない。
使われ方：二重 Čech の外重みへの増強と整合する重み変更。 -/
def comparisonIso : weightedFunctor K I J W ⋙ L ≅ HomotopyCones.functor K I J ⋙ L := by
  let dw := derivedData K I J W hW L Q
  let dc := derivedData K I J (HomotopyCones.weight K I J)
    (HomotopyCones.weight_isCofibrant K I J) L Q
  let aw := DerivedData.constantAdjunction K I J W hW q hq hcof L Q constant e dw
  let ac := DerivedData.constantAdjunction K I J (HomotopyCones.weight K I J)
    (HomotopyCones.weight_isCofibrant K I J) (HomotopyCones.weightComparison K I J)
    (HomotopyCones.weightComparison_objectwiseWeakEquivalence K I J) hcof L Q constant e dc
  exact DerivedData.computationIso K I J W hW L Q dw ≪≫
    Functor.isoWhiskerLeft Q (aw.rightAdjointUniq ac) ≪≫
    (DerivedData.computationIso K I J (HomotopyCones.weight K I J)
      (HomotopyCones.weight_isCofibrant K I J) L Q dc).symm

end SerrePositivity.KST.Descent.CofibrantCechWeight
