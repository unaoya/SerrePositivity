module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Monoidal.ModelCategory
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Cofibrant objects and tensor powers in monoidal model categories -/

@[expose] public section
universe u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MonoidalCategory

namespace SerrePositivity.Quillen

lemma map_isCofibrant {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] [ModelCategory D]
    (L : C ⥤ D) [L.IsLeftAdjoint] [IsLeftQuillen L] (X : C) [IsCofibrant X] :
    IsCofibrant (L.obj X) := by
  have := map_cofibration L (initial.to X)
  exact (isCofibrant_iff_of_isInitial (L.map (initial.to X))
    (initialIsInitial.isInitialObj L (⊥_ C))).2 inferInstance

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [IsQuillenBifunctor (curriedTensor C)]

lemma tensorLeft_isLeftQuillen (X : C) [IsCofibrant X] : IsLeftQuillen (tensorLeft X) := by
  have : ∀ Y : C, ((curriedTensor C).flip.obj Y).IsLeftAdjoint :=
    fun Y ↦ inferInstanceAs (tensorRight Y).IsLeftAdjoint
  exact isLeftQuillen_obj_of_cofibrant (curriedTensor C) X

lemma tensorRight_isLeftQuillen (X : C) [IsCofibrant X] : IsLeftQuillen (tensorRight X) := by
  have h := tensorLeft_isLeftQuillen X
  let e := BraidedCategory.tensorLeftIsoTensorRight X
  constructor
  · intro A B f hf
    have hm := h.map_cofibrations f hf
    change cofibrations C ((tensorLeft X).map f) at hm
    exact ((cofibrations C).arrow_mk_iso_iff
      (Arrow.isoMk (e.app A) (e.app B) (e.hom.naturality f).symm)).mp hm
  · intro A B f hf
    have hm := h.map_trivialCofibrations f hf
    change trivialCofibrations C ((tensorLeft X).map f) at hm
    exact ((trivialCofibrations C).arrow_mk_iso_iff
      (Arrow.isoMk (e.app A) (e.app B) (e.hom.naturality f).symm)).mp hm

lemma tensor_isCofibrant (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    IsCofibrant (X ⊗ Y) := by
  have := tensorLeft_isLeftQuillen X
  exact map_isCofibrant (tensorLeft X) Y

lemma tensorPower_isCofibrant (X : C) [IsCofibrant X] [IsCofibrant (𝟙_ C)] (n : ℕ) :
    IsCofibrant (TensorPowers.power X n) := by
  induction n with
  | zero => exact inferInstanceAs (IsCofibrant (𝟙_ C))
  | succ n ih =>
    have := ih
    exact tensor_isCofibrant X (TensorPowers.power X n)
end SerrePositivity.Quillen

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.1.7.6" (partial := component) "仮定：余ファイブラントな X,Y と、組紐付き閉モノイダルモデル圏のテンソルの Quillen 条件（Lean が強い：組紐付き閉の場合）。結論：X⊗Y が余ファイブラントであること（HA の Aᶜ がテンソルで閉じる部分に一致）。弱同値の両側保存と、局所化上のモノイダル ∞ 構造はこの型に含まれない。"] _root_.SerrePositivity.Quillen.tensor_isCofibrant
attribute [cite HA "4.5.4.10" (partial := special) "仮定：Quillen テンソルを持つモデル圏で底の二つの余ファイブレーションまたは余ファイブラント対象（Lean が強い：添字圏は両方とも一点、対象については組紐付き閉の場合）。結論：押し出し積が余ファイブレーション、テンソル積が余ファイブラント（その場合に二つの結論が一致）。一般の二つの射影図式の外部積は型に含まれない。"] _root_.SerrePositivity.Quillen.tensor_isCofibrant
