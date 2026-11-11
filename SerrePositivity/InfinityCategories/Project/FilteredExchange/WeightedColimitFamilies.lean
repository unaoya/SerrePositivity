module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimit

/-!
概要：パラメータ付きの重み付き脚から coend の射の族を構成する。
方針：tensor が保つ cowedge の余極限の普遍性を使う。
規約：dinaturality を全パラメータで厳密に要求する。
使われ方：Bousfield–Kan augmentation の収縮ホモトピーの貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I]

/-- 概要：パラメータ付きの dinatural な脚を coend からの射の族へ降下させる。
方針：tensor 後の cowedge の実際の余極限性を適用する。
規約：パラメータ A と標的 Y は任意。使われ方：全体のホモトピーの構成。 -/
def weightedColimitFamily (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (A Y : SSet.{u})
    (d : ∀ i, (F.obj i ⊗ W.obj (Opposite.op i)) ⊗ A ⟶ Y)
    (hd : ∀ {i j} (f : i ⟶ j), ((F.obj i ◁ W.map f.op) ▷ A) ≫ d i =
      ((F.map f ▷ W.obj (Opposite.op j)) ▷ A) ≫ d j) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F ⊗ A ⟶ Y :=
  Cowedge.IsColimit.desc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitTensorCowedge_isColimit W F A) d (by
    intro i j f
    exact hd f)

/-- 概要：降下させた族は各重み付き脚上で元の族に一致する。
方針：cowedge の余極限の計算則。
規約：パラメータ全体での厳密な等式。使われ方：ホモトピーの端点と自然性。 -/
lemma weightedColimitι_family (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (A Y : SSet.{u})
    (d : ∀ i, (F.obj i ⊗ W.obj (Opposite.op i)) ⊗ A ⟶ Y)
    (hd : ∀ {i j} (f : i ⟶ j), ((F.obj i ◁ W.map f.op) ▷ A) ≫ d i =
      ((F.map f ▷ W.obj (Opposite.op j)) ▷ A) ≫ d j) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ▷ A) ≫ weightedColimitFamily W F A Y d hd = d i :=
  Cowedge.IsColimit.π_desc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitTensorCowedge_isColimit W F A) d _ i

end SerrePositivity.InfinityCategories.Project.FilteredExchange
