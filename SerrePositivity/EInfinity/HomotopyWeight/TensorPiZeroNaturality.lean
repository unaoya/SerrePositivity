module

public import SerrePositivity.EInfinity.HomotopyWeight.TensorPiZero

/-!
# 係数 frame の射に関する重み付き錐の π₀ 比較の自然性

概要：Hovey §5.4 の錐の連結成分の比較は実際の重み付き実現の前合成と両立する。
方針：二つの随伴の Hom 自然性と零次同型の自然性を使う。
規約：実現の射は既存の随伴の mate そのものを使う。
使われ方：係数の弱同値から一般 homotopy 極限の擬同型を検出する。
-/

@[expose] public section

noncomputable section

universe u v w t

namespace SerrePositivity.EInfinity.HomotopyWeight

open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u})

omit [ModelCategory C] in
/-- 概要：テンソル実現の Hom 随伴は係数 frame の射に自然（Hovey §5.4）。
方針：重み付き実現の mate の自然性を錐の随伴へ移す。
規約：二つの実際の随伴の合成を使う。
使われ方：標準 frame の Hom 同型の係数自然性。 -/
lemma tensorRealization_homEquiv_frame_naturality
    {B B' : K ⥤ SimplexCategory ⥤ C} (a : B ⟶ B') (X : SSet.{u}) (Y : C)
    (f : (tensorRealization K W B').obj X ⟶ Y) :
    (tensorRealizationAdjunction K W B).homEquiv X Y
        ((FrameWeightRealization.map K a).app ((WeightedCones.tensorDiagram Kᵒᵖ W).obj X) ≫ f) =
      (tensorRealizationAdjunction K W B').homEquiv X Y f ≫
        (WeightedCones.coneSpace Kᵒᵖ W).map
          (((FrameWeightRealization.homFamily K).map a.op).app Y) := by
  simp only [tensorRealizationAdjunction, Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [FrameWeightRealization.homEquiv_frame_naturality]
  exact (WeightedCones.adjunction Kᵒᵖ W).homEquiv_naturality_right _ _

omit [ModelCategory C] in
/-- 概要：標準 frame の Hom 同型は係数の実際の射に自然（Hovey §5.4）。
方針：随伴の係数自然性を全単体で Yoneda 同型に通す。
規約：構成済みの重み付き実現の射を使う。
使われ方：錐の連結成分の自然性を証明する。 -/
lemma tensorFrameHomIso_source_naturality {B B' : K ⥤ SimplexCategory ⥤ C}
    (a : B ⟶ B') (Y : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (Functor.whiskerLeft
        (SSet.stdSimplex ⋙ WeightedCones.tensorDiagram Kᵒᵖ W)
        (FrameWeightRealization.map K a))).app Y ≫ (tensorFrameHomIso K W B).hom.app Y =
      (tensorFrameHomIso K W B').hom.app Y ≫ (WeightedCones.coneSpace Kᵒᵖ W).map
        (((FrameWeightRealization.homFamily K).map a.op).app Y) := by
  ext n f
  change SSet.yonedaEquiv ((tensorRealizationAdjunction K W B).homEquiv _ Y (_ ≫ f)) =
    (((WeightedCones.coneSpace Kᵒᵖ W).map
      (((FrameWeightRealization.homFamily K).map a.op).app Y)).app n)
        (SSet.yonedaEquiv ((tensorRealizationAdjunction K W B').homEquiv _ Y f))
  rw [← SSet.yonedaEquiv_comp]
  exact congrArg SSet.yonedaEquiv (tensorRealization_homEquiv_frame_naturality K W a _ Y f)

variable (hW : (boundaries Kᵒᵖ).rlp.llp (initial.to W))
  {B B' : K ⥤ SimplexCategory ⥤ C}
  (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
  (hB' : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B'.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((B.obj k).map f))
  (hconst' : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((B'.obj k).map f))
  {D : Type w} [Category.{t} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- 概要：錐の π₀ 比較は係数射の実現による前合成に自然（Hovey §5.4）。
方針：零単体の表示で Hom 同型の自然性と零次の重み同型の自然性を使う。
規約：局所化した射は実際の重み付き実現の同じ射。
使われ方：重み付き錐の不変性から実現対象の弱同値性を導く。 -/
lemma frameConePiZeroLocalizationEquiv_source (a : B ⟶ B') (Y : C) [IsFibrant Y]
    (z : SSet.π₀ ((frameCone K W B').obj Y)) :
    frameConePiZeroLocalizationEquiv K W B hW hB hconst L Y
      (SSet.mapπ₀ ((WeightedCones.coneSpace Kᵒᵖ W).map
        (((FrameWeightRealization.homFamily K).map a.op).app Y)) z) =
      L.map ((FrameWeightRealization.map K a).app W) ≫
        frameConePiZeroLocalizationEquiv K W B' hW hB' hconst' L Y z := by
  let e := (SSet.π₀Functor.mapIso ((tensorFrameHomIso K W B').app Y)).toEquiv
  obtain ⟨z, rfl⟩ := e.surjective z
  induction z using SSet.π₀.rec with | mk f =>
  change frameConePiZeroLocalizationEquiv K W B hW hB hconst L Y
      (SSet.mapπ₀ _ (SSet.mapπ₀ ((tensorFrameHomIso K W B').app Y).hom (SSet.π₀.mk f))) =
    L.map ((FrameWeightRealization.map K a).app W) ≫
      frameConePiZeroLocalizationEquiv K W B' hW hB' hconst' L Y
        (SSet.mapπ₀ ((tensorFrameHomIso K W B').app Y).hom (SSet.π₀.mk f))
  have hn : ((tensorFrameHomIso K W B').app Y).hom ≫
      (WeightedCones.coneSpace Kᵒᵖ W).map
        (((FrameWeightRealization.homFamily K).map a.op).app Y) =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (Functor.whiskerLeft
      (SSet.stdSimplex ⋙ WeightedCones.tensorDiagram Kᵒᵖ W)
      (FrameWeightRealization.map K a))).app Y ≫ ((tensorFrameHomIso K W B).app Y).hom :=
    (tensorFrameHomIso_source_naturality K W a Y).symm
  rw [← SSet.mapπ₀_comp_apply, hn, SSet.mapπ₀_comp_apply, SSet.mapπ₀_mk]
  rw [frameConePiZeroLocalizationEquiv_mk, frameConePiZeroLocalizationEquiv_mk]
  rw [← L.map_comp, ← Category.assoc, ← L.map_comp]
  change L.map ((tensorFrameZeroIso K W B).inv ≫
      ((FrameWeightRealization.map K a).app
        ((WeightedCones.tensorDiagram Kᵒᵖ W).obj (SSet.stdSimplex.obj
          (SimplexCategory.mk 0))) ≫ f)) = _
  rw [← Category.assoc, L.map_comp]
  exact congrArg (fun g => L.map g ≫ L.map f)
    ((FrameWeightRealization.map K a).naturality (zeroTensorWeightIso Kᵒᵖ W).inv)

end SerrePositivity.EInfinity.HomotopyWeight
