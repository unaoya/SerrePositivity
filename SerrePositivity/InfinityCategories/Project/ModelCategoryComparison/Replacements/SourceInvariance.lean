module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.TargetInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeBoundaryTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexModelCategory

/-!
# 単体集合のモデル構造を使わない frame Hom の始域不変性

概要：Hovey §5 の Reedy cofibrant な frame の弱同値は Hom を anodyne 反転後に同型にする。
方針：相対 latching の境界持ち上げと Reedy モデルの Brown 分解を使う。
規約：単体集合の完全なモデル構造や弱同値類は入力しない。
使われ方：E 代数の導来写像空間と右 frame の重み付き end の不変性。
-/

@[expose] public section

noncomputable section

universe u v u' v'

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory Limits HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 概要：Reedy 自明 cofibration の Hom は境界の右類に入る（Hovey §5）。
方針：相対 latching 射と fibrant な終域の間の持ち上げを使う。
規約：実際の境界生成族による判定で、単体集合のモデル構造は不要。
使われ方：frame の自明 cofibration の反転。 -/
lemma source_boundary_rlp {A B : SimplexCategory ⥤ C} (a : A ⟶ B)
    (ha : reedyLeft simplex (trivialCofibrations C) a) (target : C) [IsFibrant target] :
    SSet.modelCategoryQuillen.I.rlp ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app target) := by
  intro X Z i hi
  obtain ⟨n⟩ := hi
  have : HasLiftingProperty (relativeLatchingMap simplex (SimplexCategory.mk n) a)
      (terminal.from (C := C) target) :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (ha _) (mem_fibrations _)
  exact boundary_source_lifting a n

variable {D : Type u'} [Category.{v'} D] (L : SSet.{v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL

/-- 概要：Reedy 自明 cofibration の Hom は anodyne 反転後に同型（Hovey §5）。
方針：境界の右類からすべての単射の右類へ移し、具体的な収縮を使う。
規約：値圏は任意の通常の圏。
使われ方：始域の Brown 分解の二つの左射の像を反転する。 -/
lemma source_trivialCofibration_isIso {A B : SimplexCategory ⥤ C} (a : A ⟶ B)
    (ha : reedyLeft simplex (trivialCofibrations C) a) (Y : C) [IsFibrant Y] :
    IsIso (L.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app Y)) :=
  SimplicialModel.MonoRightLiftingContraction.image_isIso _
    (SSet.rlp_monomorphisms.ge _ (source_boundary_rlp a ha Y)) L hL

/-- 概要：Reedy cofibrant な frame 間の弱同値の Hom は anodyne 反転後に同型（Hovey §5）。
方針：Reedy モデルの Brown 分解と、切断の像の同型性を使う。
規約：frame の Reedy cofibrancy は明示し、単体集合モデルは入力しない。
使われ方：具体的な E 代数の始域に関する導来写像空間の不変性。 -/
lemma source_weakEquivalence_isIso {A B : SimplexCategory ⥤ C} (a : A ⟶ B)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (ha : ∀ n, weakEquivalences C (a.app n)) (Y : C) [IsFibrant Y] :
    IsIso (L.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app Y)) := by
  let := simplexModelCategory C
  have : IsCofibrant A := ⟨hA⟩
  have : IsCofibrant B := ⟨hB⟩
  have : WeakEquivalence a := ⟨ha⟩
  let h := Classical.choice (inferInstance : Nonempty (CofibrantBrownFactorization a))
  have : Cofibration h.i := (cofibration_iff _).mpr h.hi
  have hi : reedyLeft simplex (trivialCofibrations C) h.i :=
    (reedyLeft_trivialCofibrations_iff simplex h.i).mpr
      ⟨h.hi, mem_weakEquivalences h.i⟩
  have hs : reedyLeft simplex (trivialCofibrations C) h.s :=
    (reedyLeft_trivialCofibrations_iff simplex h.s).mpr
      ⟨mem_cofibrations h.s, mem_weakEquivalences h.s⟩
  let R : (SimplexCategory ⥤ C)ᵒᵖ ⥤ D :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (evaluation C SSet.{v}).obj Y ⋙ L
  have : IsIso (R.map h.i.op) := source_trivialCofibration_isIso L hL h.i hi Y
  have : IsIso (R.map h.s.op) := source_trivialCofibration_isIso L hL h.s hs Y
  have he : R.map h.p.op ≫ R.map h.s.op = 𝟙 _ := by
    rw [← R.map_comp]
    change R.map (h.s ≫ h.p).op = _
    rw [h.s_p]
    exact R.map_id _
  have hp : R.map h.p.op = inv (R.map h.s.op) := by
    apply (cancel_mono (R.map h.s.op)).mp
    simpa only [IsIso.inv_hom_id] using he
  have : IsIso (R.map h.p.op) := by rw [hp]; infer_instance
  have hf : R.map h.p.op ≫ R.map h.i.op = R.map a.op := by
    rw [← R.map_comp]
    exact congrArg R.map (congrArg Quiver.Hom.op h.fac)
  change IsIso (R.map a.op)
  rw [← hf]
  infer_instance

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
