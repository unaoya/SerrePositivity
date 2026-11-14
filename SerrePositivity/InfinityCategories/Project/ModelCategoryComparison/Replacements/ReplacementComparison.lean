module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SourceInvariance
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.TargetInvariance
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.Comparison
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetComparison

/-!
# 分解と終域置換の比較を anodyne 反転で扱う

概要：既存の自然な共同比較の四つの Hom 射は anodyne 反転後に同型。
方針：元の Reedy cofibrancy・各値の弱同値性と Brown 不変性を接続する。
規約：単体集合のモデル構造と cofibration 類の同定は入力しない。
使われ方：実モデル圏の分解・right frame の選択比較の入口。
-/

@[expose] public section
noncomputable section
universe u v u' v'
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type u'} [Category.{v'} D] (L : SSet.{v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

section LocalizedComparisons
include hL

/-- 概要：分解の共同比較の左 Hom 射は反転後に同型。
方針：同じ左射の各値の弱同値性に始域不変性を使う。
規約：指定した自然変換自身を比較する。
使われ方：ResolutionComparison.homLeft のモデル非依存の代替判定。 -/
lemma resolutionComparison_left_isIso
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (q q' : CofibrantResolutionFamily (C := C) simplex)
    (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    IsIso (L.map (((ResolutionComparison.homLeft cof q q' R).app X).app Y)) := by
  have := hR Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_weakEquivalence_isIso L hL ((ResolutionComparison.left cof q q').app X.unop)
    ((ResolutionComparison.common cof q q').cofibrant X.unop) (q.cofibrant X.unop)
    (ResolutionComparison.left_weakEquivalence cof q q' X.unop) (R.obj Y)

/-- 概要：分解の共同比較の右 Hom 射は反転後に同型。
方針：同じ右射の各値の弱同値性に始域不変性を使う。
規約：指定した自然変換自身を比較する。
使われ方：ResolutionComparison.homRight のモデル非依存の代替判定。 -/
lemma resolutionComparison_right_isIso
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (q q' : CofibrantResolutionFamily (C := C) simplex)
    (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    IsIso (L.map (((ResolutionComparison.homRight cof q q' R).app X).app Y)) := by
  have := hR Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_weakEquivalence_isIso L hL ((ResolutionComparison.right cof q q').app X.unop)
    ((ResolutionComparison.common cof q q').cofibrant X.unop) (q'.cofibrant X.unop)
    (ResolutionComparison.right_weakEquivalence cof q q' X.unop) (R.obj Y)

/-- 概要：終域置換の共同比較の左 Hom 射は反転後に同型。
方針：元の左射の弱同値性と両終域の fibrancy に終域不変性を使う。
規約：元の分解と同じ標的自然変換を保持する。
使われ方：TargetComparison.homLeft のモデル非依存の代替判定。 -/
lemma targetComparison_left_isIso
    (fib fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C))
    (q : CofibrantResolutionFamily (C := C) simplex) (X : Cᵒᵖ) (Y : C) :
    IsIso (L.map (((TargetComparison.homLeft fib fib₁ fib₂ q.obj).app X).app Y)) := by
  have := fibrantTarget_isFibrant fib₁ Y
  have := TargetComparison.isFibrant_obj fib fib₁ fib₂ Y
  have : WeakEquivalence ((TargetComparison.left fib fib₁ fib₂).app Y) :=
    ⟨(TargetComparison.left_trivialCofibration fib fib₁ fib₂ Y).2⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_weakEquivalence_isIso (q.obj.obj X.unop) (q.cofibrant X.unop) L hL
    ((TargetComparison.left fib fib₁ fib₂).app Y)

/-- 概要：終域置換の共同比較の右 Hom 射は反転後に同型。
方針：元の右射の弱同値性と両終域の fibrancy に終域不変性を使う。
規約：元の分解と同じ標的自然変換を保持する。
使われ方：TargetComparison.homRight のモデル非依存の代替判定。 -/
lemma targetComparison_right_isIso
    (fib fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C))
    (q : CofibrantResolutionFamily (C := C) simplex) (X : Cᵒᵖ) (Y : C) :
    IsIso (L.map (((TargetComparison.homRight fib fib₁ fib₂ q.obj).app X).app Y)) := by
  have := fibrantTarget_isFibrant fib₂ Y
  have := TargetComparison.isFibrant_obj fib fib₁ fib₂ Y
  have : WeakEquivalence ((TargetComparison.right fib fib₁ fib₂).app Y) :=
    ⟨(TargetComparison.right_trivialCofibration fib fib₁ fib₂ Y).2⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_weakEquivalence_isIso (q.obj.obj X.unop) (q.cofibrant X.unop) L hL
    ((TargetComparison.right fib fib₁ fib₂).app Y)

end LocalizedComparisons

/-- 概要：分解の左 Hom 比較自身は弱ホモトピー同値。
方針：anodyne 局所化での反転性を全 Kan 標的による判定へ渡す。
規約：単体集合のモデル構造を要求しない。
使われ方：ResolutionComparison の左の弱同値判定の代替。 -/
lemma resolutionComparison_left_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (q q' : CofibrantResolutionFamily (C := C) simplex)
    (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (((ResolutionComparison.homLeft cof q q' R).app X).app Y) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (resolutionComparison_left_isIso SimplicialModel.AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions) cof q q' R hR X Y)

/-- 概要：分解の右 Hom 比較自身は弱ホモトピー同値。
方針：同じ右射の anodyne 反転性を弱同値判定へ渡す。
規約：単体集合のモデル構造を要求しない。
使われ方：ResolutionComparison の右の弱同値判定の代替。 -/
lemma resolutionComparison_right_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (q q' : CofibrantResolutionFamily (C := C) simplex)
    (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (((ResolutionComparison.homRight cof q q' R).app X).app Y) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (resolutionComparison_right_isIso SimplicialModel.AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions) cof q q' R hR X Y)

/-- 概要：終域置換の左 Hom 比較自身は弱ホモトピー同値。
方針：同じ左射の anodyne 反転性を弱同値判定へ渡す。
規約：単体集合のモデル構造を要求しない。
使われ方：TargetComparison の左の弱同値判定の代替。 -/
lemma targetComparison_left_isWeakHomotopyEquivalence
    (fib fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C))
    (q : CofibrantResolutionFamily (C := C) simplex) (X : Cᵒᵖ) (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (((TargetComparison.homLeft fib fib₁ fib₂ q.obj).app X).app Y) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (targetComparison_left_isIso SimplicialModel.AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions) fib fib₁ fib₂ q X Y)

/-- 概要：終域置換の右 Hom 比較自身は弱ホモトピー同値。
方針：同じ右射の anodyne 反転性を弱同値判定へ渡す。
規約：単体集合のモデル構造を要求しない。
使われ方：TargetComparison の右の弱同値判定の代替。 -/
lemma targetComparison_right_isWeakHomotopyEquivalence
    (fib fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C))
    (q : CofibrantResolutionFamily (C := C) simplex) (X : Cᵒᵖ) (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (((TargetComparison.homRight fib fib₁ fib₂ q.obj).app X).app Y) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (targetComparison_right_isIso SimplicialModel.AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions) fib fib₁ fib₂ q X Y)

/-- 概要：弱く増大された frame への左 Hom 比較自身は弱ホモトピー同値。
方針：既存の左比較の anodyne 反転性を弱同値判定へ渡す。
規約：単体集合のモデル構造を要求しない。
使われ方：FrameComparison.homLeft_weakEquivalence の代替。 -/
lemma frameComparison_left_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (q : CofibrantResolutionFamily (C := C) simplex) (p : CosimplicialFrameFamily (C := C))
    (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (((FrameComparison.homLeft cof q p R).app X).app Y) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.comparison_left_isIso cof q p R hR SimplicialModel.AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions) X Y)

/-- 概要：弱く増大された frame への右 Hom 比較自身は弱ホモトピー同値。
方針：既存の右比較の anodyne 反転性を弱同値判定へ渡す。
規約：単体集合のモデル構造を要求しない。
使われ方：FrameComparison.homRight_weakEquivalence の代替。 -/
lemma frameComparison_right_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (q : CofibrantResolutionFamily (C := C) simplex) (p : CosimplicialFrameFamily (C := C))
    (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (((FrameComparison.homRight cof q p R).app X).app Y) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.comparison_right_isIso cof q p R hR SimplicialModel.AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions) X Y)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
