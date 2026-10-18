module

public import SerrePositivity.KST.Descent.PresheafBaseChange

/-!
# 増強を含む実際の図式比較の retract

## 概要
基底上の図式への前層の制限と、基底の値からの指定増強を自然な比較として構成する。

## 方針
各対象の構造射を前層で引き戻し、前層そのものの retract を比較射の retract へ移す。

## 規約
図式の増強先の値も保持する。図式の通常の極限や Tot は取らない。

## 使われ方
論文 補題 3.2 の有限平坦 transfer による Čech 比較の retract の入力。
-/

@[expose] public section

universe u v w t u' v'

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] {V : Type w} [Category.{t} V]
  {J : Type u'} [Category.{v'} J] {Y : C} (K : J ⥤ Over Y)

/-- 概要：基底上の各図式対象から基底自身への射（論文 補題 3.2）。
方針：対象に保持された構造射を Over の射にする。
規約：基底対象の構造射は恒等射。
使われ方：前層による指定増強。 -/
def overDiagramToBase (j : J) : K.obj j ⟶ Over.mk (𝟙 Y) :=
  Over.homMk (K.obj j).hom (Category.comp_id _)

/-- 概要：図式の基底への射は自然（論文 補題 3.2）。
方針：Over の射の構造射との可換性を使う。
規約：図式の全ての射についての恒等式。
使われ方：前層を適用した増強の自然性。 -/
theorem overDiagramToBase_naturality {i j : J} (α : i ⟶ j) :
    K.map α ≫ overDiagramToBase K j = overDiagramToBase K i := by
  apply (Over.forget Y).map_injective
  exact (K.map α).w

/-- 概要：基底の前層の値から図式への指定増強（論文 補題 3.2）。
方針：元の構造射を前層で反変に写す。
規約：対象ごとに任意の比較射を選ばない。
使われ方：Čech 比較の実際の増強。 -/
def presheafDiagramAugmentation (F : (Over Y)ᵒᵖ ⥤ V) :
    (Functor.const Jᵒᵖ).obj (F.obj (op (Over.mk (𝟙 Y)))) ⟶ K.op ⋙ F where
  app j := F.map (overDiagramToBase K j.unop).op
  naturality {i j} α := by
    change 𝟙 _ ≫ F.map (overDiagramToBase K j.unop).op =
      F.map (overDiagramToBase K i.unop).op ≫ F.map (K.map α.unop).op
    rw [Category.id_comp, ← F.map_comp]
    exact (congrArg F.map (congrArg Quiver.Hom.op
      (overDiagramToBase_naturality K α.unop))).symm

/-- 概要：基底の前層の値を定数図式にする関手（論文 補題 3.2）。
方針：増強先の評価と定数図式関手を合成する。
規約：増強先の値を図式の各次数と別に保持する。
使われ方：指定増強を自然な比較として扱う始域。 -/
def presheafAugmentationSource : ((Over Y)ᵒᵖ ⥤ V) ⥤ Jᵒᵖ ⥤ V :=
  (evaluation _ _).obj (op (Over.mk (𝟙 Y))) ⋙ Functor.const Jᵒᵖ

/-- 概要：基底上の図式に前層を制限する関手（論文 補題 3.2）。
方針：反対図式の前合成関手を使う。
規約：図式の全ての射も写す。
使われ方：指定増強を自然な比較として扱う終域。 -/
def presheafAugmentationTarget : ((Over Y)ᵒᵖ ⥤ V) ⥤ Jᵒᵖ ⥤ V :=
  (Functor.whiskeringLeft _ _ _).obj K.op

/-- 概要：指定増強は前層についても自然（論文 補題 3.2）。
方針：前層間の自然変換の構造射についての自然性を使う。
規約：増強を含む図式全体の比較を保持する。
使われ方：前層の transfer retract を比較射の retract へ移す。 -/
def presheafAugmentationComparison :
    presheafAugmentationSource (V := V) (J := J) (Y := Y) ⟶
      presheafAugmentationTarget K where
  app := presheafDiagramAugmentation K
  naturality {F G} α := by
    ext j
    exact (α.naturality (overDiagramToBase K j.unop).op).symm

variable [HasPullbacks C] [Preadditive V] [Linear ℚ V]

/-- 概要：実際の底変換 transfer は増強図式の比較射を retract にする（論文 補題 3.2）。
方針：局所 rank 公式で前層の retract を作り、指定増強の自然性で矢の圏へ移す。
規約：transfer の存在と局所 rank 公式は明示した入力。Tot の性質は含めない。
使われ方：L9 の実際の Tot 関手に渡す増強比較の retract。 -/
noncomputable def BaseChangeTransfer.augmentationRetract {X : C} {f : X ⟶ Y}
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F)) :
    RetractArrow (presheafDiagramAugmentation K (overPresheaf (Y := Y) F))
      (presheafDiagramAugmentation K (baseChangedPresheaf f F)) :=
  naturalComparisonRetract (presheafAugmentationSource (J := J) (Y := Y))
    (presheafAugmentationTarget K) (presheafAugmentationComparison K)
    (BaseChangeTransfer.retract f tr rank positive rank_identity)

end SerrePositivity.KST.Descent
