module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：一般の重み付き coend からの内部 Hom を、反変 Hom の重み付き end と同定する。
方針：普遍脚の評価と end の評価を二度 curry・uncurry して両逆を構成する。
規約：全単体の同型であり、Kan 性やモデル構造の存在を仮定しない。
使われ方：HTT 4.2.4.1、γ3c の Bousfield–Kan 余極限の写像空間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 普遍的な脚の評価を二度 curry する前の自然性。 -/
lemma weightedColimitHomSection_naturality (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (Y A : SSet.{u}) (e : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F ⊗ A ⟶ Y) {i j : I} (f : i ⟶ j) :
    (W.map f.op ▷ A) ≫ curry ((α_ (F.obj i) (W.obj (Opposite.op i)) A).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ▷ A) ≫ e) =
    curry ((α_ (F.obj j) (W.obj (Opposite.op j)) A).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F j ▷ A) ≫ e) ≫ (pre (F.map f)).app Y := by
  erw [← curry_natural_left, curry_pre_app]
  apply congrArg curry
  rw [associator_inv_naturality_middle_assoc, associator_inv_naturality_left_assoc]
  simp only [← comp_whiskerRight_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_condition]

/-- 重み付き余極限の Hom から各反変 Hom へのパラメータ付き評価。 -/
def weightedColimitHomSection (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    W ⊗ (Functor.const Iᵒᵖ).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).obj Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y where
  app i := curry ((α_ (F.obj i.unop) (W.obj i) _).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i.unop ▷ _) ≫ (ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).app Y)
  naturality i j g := by
    simpa [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram] using
      weightedColimitHomSection_naturality W F Y _
        ((ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).app Y) g.unop

/-- coend の内部 Hom から重み付き end への実際の単体集合の比較射。 -/
def weightedColimitHomComparison (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).obj Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (weightedColimitHomSection W F Y)

/-- 比較射の各成分は普遍的な脚による評価を二度 curry した射。 -/
lemma weightedColimitHomComparison_π (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u})
    (i : Iᵒᵖ) :
    weightedColimitHomComparison W F Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) i =
      curry (curry ((α_ (F.obj i.unop) (W.obj i) _).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i.unop ▷ _) ≫ (ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).app Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π _ i

/-- end の普遍評価を coend の tensor から評価する各成分。 -/
def weightedColimitEndEvaluationι (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) (i : I) :
    (F.obj i ⊗ W.obj (Opposite.op i)) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) ⟶ Y :=
  (α_ (F.obj i) (W.obj (Opposite.op i)) _).hom ≫
    uncurry (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) (Opposite.op i)))

/-- 二重 uncurry は Hom の両変数の自然性を tensor の dinaturality へ移す。 -/
lemma weightedColimit_doubleUncurry {A B C D P Y : SSet.{u}} (f : B ⟶ A) (g : C ⟶ D)
    (p : P ⟶ (ihom B).obj ((ihom D).obj Y)) (q : P ⟶ (ihom A).obj ((ihom C).obj Y))
    (h : p ≫ (ihom B).map ((pre g).app Y) = q ≫ (pre f).app ((ihom C).obj Y)) :
    C ◁ (f ▷ P) ≫ uncurry (uncurry q) =
      g ▷ (B ⊗ P) ≫ uncurry (uncurry p) := by
  have h' := congrArg uncurry h
  rw [uncurry_natural_right, uncurry_pre_app] at h'
  have h'' := congrArg uncurry h'
  rw [uncurry_pre_app, uncurry_natural_left] at h''
  exact h''.symm

set_option maxHeartbeats 800000 in
-- The explicit end carries a chosen limit cone; normalizing its Hom types needs extra fuel.
/-- end の自然性は普遍評価の dinaturality を与える。 -/
lemma weightedColimitEndEvaluation_condition (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (Y : SSet.{u}) {i j : I} (f : i ⟶ j) :
    (F.obj i ◁ W.map f.op) ▷ _ ≫ weightedColimitEndEvaluationι W F Y i =
      (F.map f ▷ W.obj (Opposite.op j)) ▷ _ ≫ weightedColimitEndEvaluationι W F Y j := by
  unfold weightedColimitEndEvaluationι
  rw [associator_naturality_middle_assoc, associator_naturality_left_assoc]
  apply congrArg ((α_ (F.obj i) (W.obj (Opposite.op j)) _).hom ≫ ·)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_condition W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) f.op
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) (Opposite.op j) ≫
      (ihom (W.obj (Opposite.op j))).map ((pre (F.map f)).app Y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) (Opposite.op i) ≫
      (pre (W.map f.op)).app ((ihom (F.obj i)).obj Y) at h
  exact weightedColimit_doubleUncurry (W.map f.op) (F.map f) _ _ h

/-- coend の tensor から end の普遍評価へ降下する。 -/
def weightedColimitEndEvaluation (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) ⟶ Y :=
  Cowedge.IsColimit.desc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitTensorCowedge_isColimit W F _)
    (weightedColimitEndEvaluationι W F Y)
    (fun {_ _} f ↦ weightedColimitEndEvaluation_condition W F Y f)

/-- 降下した普遍評価は各 coend 成分上で元の評価に一致する。 -/
lemma weightedColimitι_endEvaluation (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (Y : SSet.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ▷ _ ≫ weightedColimitEndEvaluation W F Y =
      weightedColimitEndEvaluationι W F Y i :=
  Cowedge.IsColimit.π_desc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitTensorCowedge_isColimit W F _) _ _ i

/-- 重み付き end から coend の内部 Hom への逆比較。 -/
def weightedColimitHomInverse (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).obj Y :=
  curry (weightedColimitEndEvaluation W F Y)

/-- 逆比較の uncurry は coend の全成分で普遍評価。 -/
lemma weightedColimitι_homInverse (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (Y : SSet.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ▷ _ ≫ uncurry (weightedColimitHomInverse W F Y) =
      weightedColimitEndEvaluationι W F Y i := by
  rw [weightedColimitHomInverse, uncurry_curry, weightedColimitι_endEvaluation]

set_option maxHeartbeats 800000 in
-- The explicit end carries a chosen limit cone; normalizing its Hom types needs extra fuel.
/-- 逆比較の後に比較を行うと end の恒等射。 -/
lemma weightedColimitHomInverse_comparison (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    weightedColimitHomInverse W F Y ≫ weightedColimitHomComparison W F Y = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  cases i
  rw [Category.assoc, weightedColimitHomComparison_π, Category.id_comp,
    ← curry_natural_left, ← curry_natural_left]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← uncurry_eq]
  erw [weightedColimitι_homInverse]
  unfold weightedColimitEndEvaluationι
  erw [Iso.inv_hom_id_assoc, curry_uncurry, curry_uncurry]
  rfl

set_option maxHeartbeats 800000 in
-- The explicit end carries a chosen limit cone; normalizing its Hom types needs extra fuel.
/-- 比較の後に逆比較を行うと内部 Hom の恒等射。 -/
lemma weightedColimitHomComparison_inverse (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    weightedColimitHomComparison W F Y ≫ weightedColimitHomInverse W F Y = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_id_eq_ev]
  apply Cowedge.IsColimit.hom_ext (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitTensorCowedge_isColimit W F _)
  intro i
  change I at i
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ▷ _) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F ◁ weightedColimitHomComparison W F Y) ≫
        uncurry (weightedColimitHomInverse W F Y) =
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ▷ _ ≫ (ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).app Y
  rw [← whisker_exchange_assoc]
  erw [weightedColimitι_homInverse]
  unfold weightedColimitEndEvaluationι
  erw [associator_naturality_right_assoc, ← uncurry_natural_left,
    ← uncurry_natural_left, weightedColimitHomComparison_π]
  simp only [uncurry_curry, Iso.hom_inv_id_assoc]
/-- Hom(coend,Y) は重み付き end に全単体で自然に同型。 -/
def weightedColimitHomIso (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).obj Y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) where
  hom := weightedColimitHomComparison W F Y
  inv := weightedColimitHomInverse W F Y
  hom_inv_id := weightedColimitHomComparison_inverse W F Y
  inv_hom_id := weightedColimitHomInverse_comparison W F Y

/-- 終域の射は反変 Hom 係数図式の自然変換を与える。 -/
def weightedColimitHomDiagramMap (F : I ⥤ SSet.{u}) {Y Z : SSet.{u}} (f : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z where
  app i := (ihom (F.obj i.unop)).map f
  naturality _ _ g := ((pre (F.map g.unop)).naturality f).symm

/-- 終域に関する反変 Hom 係数の関手。 -/
def weightedColimitHomDiagramFunctor (F : I ⥤ SSet.{u}) : SSet.{u} ⥤ (Iᵒᵖ ⥤ SSet.{u}) where
  obj Y := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y
  map f := weightedColimitHomDiagramMap F f
  map_id Y := by
    apply NatTrans.ext
    funext i
    exact (ihom (F.obj i.unop)).map_id Y
  map_comp f g := by
    apply NatTrans.ext
    funext i
    exact (ihom (F.obj i.unop)).map_comp f g

/-- coend と end の内部 Hom 比較は終域について自然。 -/
lemma weightedColimitHomComparison_naturality (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    {Y Z : SSet.{u}} (f : Y ⟶ Z) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).map f ≫ weightedColimitHomComparison W F Z =
      weightedColimitHomComparison W F Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W (weightedColimitHomDiagramMap F f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, weightedColimitHomComparison_π, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π]
  conv_rhs => rw [← Category.assoc, weightedColimitHomComparison_π]
  change (ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).map f ≫
      curry (curry ((α_ (F.obj i.unop) (W.obj i) _).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i.unop ▷ _) ≫ (ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).app Z)) =
    curry (curry ((α_ (F.obj i.unop) (W.obj i) _).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i.unop ▷ _) ≫ (ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).app Y)) ≫
        (ihom (W.obj i)).map ((ihom (F.obj i.unop)).map f)
  rw [← curry_natural_left, ← curry_natural_left]
  conv_rhs => rw [← curry_natural_right, ← curry_natural_right]
  apply congrArg curry
  apply congrArg curry
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    ← uncurry_eq, uncurry_ihom_map]
  simp only [Category.assoc]

/-- 写像空間の同型を終域に自然な同型へ束ねる。 -/
def weightedColimitHomNatIso (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) :
    ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F) ≅ weightedColimitHomDiagramFunctor F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor W :=
  NatIso.ofComponents (weightedColimitHomIso W F) (by
    intro Y Z f
    exact weightedColimitHomComparison_naturality W F f)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
