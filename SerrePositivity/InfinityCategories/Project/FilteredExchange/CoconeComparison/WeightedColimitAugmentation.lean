module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：重み付き coend から元の図式の通常の余錐への比較射。
方針：重みの変数を忘れ、余錐の脚を coend の普遍性で降下させる。
規約：重みの可縮性・Kan 性・図式の filtered 性は不要。
使われ方：Bousfield–Kan coend から通常の colimit への augmentation。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I]

/-- 概要：通常の余錐は、重みの変数を忘れる coend からの射を定める。
方針：各成分の第一射影と余錐の脚を合成する。
規約：指定された余錐の頂点を保持する。使われ方：余極限模型の標準比較。 -/
def weightedColimitAugmentation (W : Iᵒᵖ ⥤ SSet.{u}) {F : I ⥤ SSet.{u}} (c : Cocone F) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F ⟶ c.pt :=
  coend.desc (fun i ↦ fst (F.obj i) (W.obj (Opposite.op i)) ≫ c.ι.app i) (by
    intro i j f
    change (F.obj i ◁ W.map f.op) ≫ fst _ _ ≫ c.ι.app i =
      (F.map f ▷ W.obj (Opposite.op j)) ≫ fst _ _ ≫ c.ι.app j
    have h₁ : (F.obj i ◁ W.map f.op) ≫ fst _ _ = fst _ _ := rfl
    have h₂ : (F.map f ▷ W.obj (Opposite.op j)) ≫ fst _ _ = fst _ _ ≫ F.map f := rfl
    rw [← Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc, c.w f])

/-- 概要：比較射は各重み付きの脚で元の余錐の脚を回収する。
方針：coend の降下の計算則。
規約：重みの全ての高次単体での等式。使われ方：元の図式との整合。 -/
lemma weightedColimitι_augmentation (W : Iᵒᵖ ⥤ SSet.{u}) {F : I ⥤ SSet.{u}}
    (c : Cocone F) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ≫ weightedColimitAugmentation W c =
      fst (F.obj i) (W.obj (Opposite.op i)) ≫ c.ι.app i := coend.ι_desc _ _ i

/-- 概要：重み付き coend の比較は図式と余錐の射に自然。
方針：coend の全ての脚で元の自然変換と余錐の可換条件を比較する。
規約：余錐は余極限でなくてもよい。使われ方：模型比較の自然性。 -/
lemma weightedColimitAugmentation_naturality (W : Iᵒᵖ ⥤ SSet.{u})
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) (cF : Cocone F) (cG : Cocone G)
    (p : cF.pt ⟶ cG.pt) (hp : ∀ i, cF.ι.app i ≫ p = η.app i ≫ cG.ι.app i) :
    weightedColimitAugmentation W cF ≫ p =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitMap W η ≫ weightedColimitAugmentation W cG := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro i
  rw [reassoc_of% weightedColimitι_augmentation, hp i,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι_map, weightedColimitι_augmentation]
  have h : (η.app i ▷ W.obj (Opposite.op i)) ≫ fst _ _ = fst _ _ ≫ η.app i := rfl
  simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ cG.ι.app i) h.symm

end SerrePositivity.InfinityCategories.Project.FilteredExchange
