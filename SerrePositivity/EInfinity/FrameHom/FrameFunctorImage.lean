module

public import SerrePositivity.EInfinity.FrameHom.FrameLeftRoofPostcompose
public import SerrePositivity.EInfinity.FrameHom.FrameIndexAugmentation
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection
public import SerrePositivity.EInfinity.Hammock.RelativeColimitMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor

/-!
概要：元の全 frame roof は相対関手の像の同じ全 frame roof に一致する。
方針：元の Hom の全単体と二列の全成分を関手で送る。
規約：元の augmentation・全作用素・全 hammock 比較射を保持する。
使われ方：bifibrant 部分圏の実比較を ambient モデル圏へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory Opposite Hammock
open SerrePositivity.HomotopyFunctionComplex
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative]
  {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) (A : SimplexCategory ⥤ C) (Y : C)

/-- 概要：元の frame の全 Hom を関手の同じ像へ送る。
方針：各射へ元の関手を作用させる。
規約：全単体・全作用素。使われ方：元の全要素圏の比較。 -/
def frameFunctorImageHom : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A ⋙ F.functor)).obj (F.functor.obj Y) where
  app _ := ↾fun f => F.functor.map f
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro h
    exact F.functor.map_comp (A.map f.unop) h

omit [W.IsMultiplicative] [V.IsMultiplicative] in
/-- 概要：充満忠実な関手の元の全 Hom 比較は実同型。
方針：各次数の射の写像の全単射性を使う。
規約：元の比較射自身。使われ方：全部分圏からの frame の回収。 -/
lemma frameFunctorImageHom_isIso [F.functor.Full] [F.functor.Faithful] :
    IsIso (frameFunctorImageHom F A Y) := by
  have (n : SimplexCategoryᵒᵖ) : IsIso ((frameFunctorImageHom F A Y).app n) := by
    apply (isIso_iff_bijective _).mpr
    exact ⟨F.functor.map_injective, F.functor.map_surjective⟩
  exact NatIso.isIso_of_isIso_app _

variable {X : C} (p : A ⟶ (Functor.const SimplexCategory).obj X)

/-- 概要：元の augmentation を同じ相対関手で送る。
方針：元の全成分へ関手を作用させ、元の自然性を写す。
規約：同じ端点を保持。使われ方：像の実 frame roof の左脚。 -/
def frameFunctorImageAugmentation : A ⋙ F.functor ⟶
    (Functor.const SimplexCategory).obj (F.functor.obj X) where
  app n := F.functor.map (p.app n)
  naturality n m f := by
    change F.functor.map (A.map f) ≫ F.functor.map (p.app m) = _ ≫ 𝟙 _
    rw [← F.functor.map_comp, p.naturality]
    simp only [Functor.const_obj_map, Category.comp_id]
    exact congrArg F.functor.map (Category.comp_id (p.app n))

variable (hp : ∀ n, W (p.app n))
  (hA : ∀ {n m} (f : n ⟶ m), W (A.map f))

/-- 概要：元の二列の全 frame 関手は同じ相対関手の像の全 frame 関手に一致する。
方針：元の三頂点・二射と全縦射の全成分を照合する。
規約：元の実関手等式。使われ方：全 nerve 比較の三角形。 -/
lemma frameLeftRoofFunctor_functorImage :
    frameLeftRoofFunctor W A p hp hA (Y := Y) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F =
      (frameFunctorImageHom F A Y).mapElements.op ⋙
        frameLeftRoofFunctor V (A ⋙ F.functor) (frameFunctorImageAugmentation F A p)
          (fun n => F.map _ (hp n)) (fun f => F.map _ (hA f)) := by
  have ho (s : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Elements)ᵒᵖ) :
      (frameLeftRoofFunctor W A p hp hA (Y := Y) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F).obj s =
        ((frameFunctorImageHom F A Y).mapElements.op ⋙
          frameLeftRoofFunctor V (A ⋙ F.functor) (frameFunctorImageAugmentation F A p)
            (fun n => F.map _ (hp n)) (fun f => F.map _ (hA f))).obj s := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
    · intro j
      fin_cases j <;> rfl
    · intro j
      fin_cases j <;> rfl
  apply Functor.hext ho
  intro s t a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho s) (ho t)
  intro j
  fin_cases j
  · exact heq_of_eq (F.functor.map_id X)
  · rfl
  · exact heq_of_eq (F.functor.map_id Y)

/-- 概要：同じ全要素圏の比較の Hom 宇宙だけを揃える。
方針：同じ up・down の間に元の全要素関手を置く。
規約：元の次数と全射。使われ方：実 nerve 比較への接続。 -/
def frameFunctorImageIndex :
    ULiftHom.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Elements)ᵒᵖ) ⥤
      ULiftHom.{max u v}
        ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A ⋙ F.functor)).obj (F.functor.obj Y)).Elements)ᵒᵖ) :=
  ULiftHom.down ⋙ (frameFunctorImageHom F A Y).mapElements.op ⋙ ULiftHom.up

/-- 概要：元の全 frame roof の nerve は同じ像の全 nerve と可換。
方針：同じ全射列を評価し、元の二列の関手等式を使う。
規約：元の実 nerve 射自身。使われ方：同じ hammock 比較の包含像。 -/
lemma frameLeftRoofNerveMap_functorImage :
    frameLeftRoofNerveMap W A p hp hA (Y := Y) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F) =
      nerveMap (frameFunctorImageIndex F A Y) ≫
        frameLeftRoofNerveMap V (A ⋙ F.functor) (frameFunctorImageAugmentation F A p)
          (fun n => F.map _ (hp n)) (fun f => F.map _ (hA f)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  change (σ ⋙ ULiftHom.down) ⋙
    (frameLeftRoofFunctor W A p hp hA (Y := Y) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F) = _
  rw [frameLeftRoofFunctor_functorImage]
  rfl

/-- 概要：同じ元の全 frame の hammock 比較は相対関手の像と可換。
方針：同じ二列の nerve 等式と元の余極限標準射の自然性を合成する。
規約：元の全比較射を保持。使われ方：ambient 弱比較からの反映。 -/
lemma frameLeftRoofColimitMap_functorImage :
    frameLeftRoofColimitMap W A p hp hA (Y := Y) ≫ Relative.colimitMap F X Y =
      nerveMap (frameFunctorImageIndex F A Y) ≫
        frameLeftRoofColimitMap V (A ⋙ F.functor) (frameFunctorImageAugmentation F A p)
          (fun n => F.map _ (hp n)) (fun f => F.map _ (hA f)) := by
  rw [frameLeftRoofColimitMap, Category.assoc, Relative.graphInclusion_colimitMap]
  change frameLeftRoofNerveMap W A p hp hA (Y := Y) ≫
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F) ≫ _ = _
  rw [← Category.assoc, frameLeftRoofNerveMap_functorImage, Category.assoc]
  rfl

omit [W.IsMultiplicative] [V.IsMultiplicative] in
/-- 概要：充満忠実な像への元の全要素圏比較は反転後に同型。
方針：同じ両 augmentation と元の Hom の実同型を消去する。
規約：元の nerve 射自身。使われ方：包含像からの実弱比較の反映。 -/
lemma frameFunctorImageIndex_localized_isIso [F.functor.Full] [F.functor.Faithful] :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap (frameFunctorImageIndex F A Y))) := by
  let Q := SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ
  have := frameFunctorImageHom_isIso F A Y
  have := SimplexTerminalNerve.liftedAugmentation_localized_isIso.{v, max u v}
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)
  have := SimplexTerminalNerve.liftedAugmentation_localized_isIso.{v, max u v}
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A ⋙ F.functor)).obj (F.functor.obj Y))
  have h := congrArg Q.map
    (SimplexTerminalNerve.liftedAugmentation_naturality.{v, max u v}
      (frameFunctorImageHom F A Y))
  simp only [Functor.map_comp] at h
  change Q.map (nerveMap (frameFunctorImageIndex F A Y)) ≫ _ = _ at h
  have hi : IsIso (Q.map (nerveMap (frameFunctorImageIndex F A Y)) ≫
      Q.map (SimplexTerminalNerve.liftedAugmentation.{v, max u v}
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A ⋙ F.functor)).obj (F.functor.obj Y)))) := by
    rw [h]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

omit [W.IsMultiplicative] [V.IsMultiplicative] in
/-- 概要：充満忠実な像への元の全要素圏 nerve 比較は弱同値。
方針：同じ反転性を全 Kan 標的で検出する。
規約：元の実比較射。使われ方：同じ frame roof の弱比較の回収。 -/
lemma frameFunctorImageIndex_isWeakHomotopyEquivalence [F.functor.Full] [F.functor.Faithful] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (nerveMap (frameFunctorImageIndex F A Y)) :=
  AnodyneWeakDetection.isWeakHomotopyEquivalence _ (frameFunctorImageIndex_localized_isIso F A Y)

end SerrePositivity.EInfinity.FrameHom
