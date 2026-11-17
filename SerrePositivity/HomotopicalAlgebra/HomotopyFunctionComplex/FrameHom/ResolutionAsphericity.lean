module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ResolutionCommaContraction
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ResolutionSpecialSpans
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# 自明 fibration の slice における実際の分解の asphericity

概要：Low 命題 3.6 の cosimplicial 分解側の全 comma 圏の可縮性を証明する。
方針：指定射の slice の充満包含を通して、同じ持ち上げ空間の収縮へ帰着する。
規約：分解の元の augmentation と全単体作用素を保持する。
使われ方：特殊な三本矢への右射の分解側のホモトピー余終性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uH vH

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}

/-- 概要：元の対象への自明 fibration の slice（Low 命題 3.6）。
方針：既存の射の類付き slice を使う。
規約：射には全ての可換三角形を含める。
使われ方：分解図式の asphericity の値圏。 -/
abbrev TrivialFibrationOver (X : C) := (trivialFibrations C).Over ⊤ X

/-- 概要：同じ分解は自明 fibration の slice への関手（Low 命題 3.6）。
方針：元の次数ごとの自明 fibration と全作用素の augmentation の自然性を束ねる。
規約：恒等射の後合成は frame の持ち上げ空間と同じ表示。
使われ方：元の分解の全 comma 圏の可縮性の対象。 -/
def resolutionOverFunctor (q : CofibrantResolution (C := C) simplex X) :
    SimplexCategory ⥤ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.TrivialFibrationOver X where
  obj n := MorphismProperty.Over.mk ⊤ (q.augmentation.app n ≫ 𝟙 X)
    ((trivialFibrations C).comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionAugmentation_trivialFibration q n)
      ((trivialFibrations C).id_mem X))
  map θ := MorphismProperty.Over.homMk (q.obj.map θ)
    (Over.w ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.overFunctor q.obj q.augmentation (𝟙 X)).map θ))
  map_id n := MorphismProperty.Over.Hom.ext (q.obj.map_id n)
  map_comp θ φ := MorphismProperty.Over.Hom.ext (q.obj.map_comp θ φ)

/-- 概要：指定射の条件を忘れると同じ元の augmentation の図式（Low 命題 3.6）。
方針：元の全対象と射を評価する。
規約：全作用素を含む厳密な関手の等式。
使われ方：充満包含による comma 比較。 -/
lemma resolutionOverFunctor_forget (q : CofibrantResolution (C := C) simplex X) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionOverFunctor q ⋙ MorphismProperty.Over.forget (trivialFibrations C) ⊤ X =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.overFunctor q.obj q.augmentation (𝟙 X) := rfl

/-- 概要：自明 fibration を終点とする元の slice の comma 圏は可縮（Low 命題 3.6）。
方針：同じ構造射の持ち上げ空間の全単体表示と収縮を使う。
規約：終点の全ての自明 fibration を扱う。
使われ方：指定射の slice への充満包含による比較の入力。 -/
lemma resolutionOverComma_image_isIso (q : CofibrantResolution (C := C) simplex X)
    (t : Over X) (ht : trivialFibrations C t.hom)
    {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.overFunctor q.obj q.augmentation (𝟙 X)) t)))) := by
  rcases t with ⟨E, ⟨⟨⟩⟩, p⟩
  have : Fibration p := ⟨ht.1⟩
  have : WeakEquivalence p := ⟨ht.2⟩
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.commaTerminal_image_isIso q.obj q.augmentation q.cofibrant p (𝟙 X) L hL

/-- 概要：元の分解は自明 fibration の slice で右 aspherical（Low 命題 3.6）。
方針：充満忠実な忘却の comma 同値と元の comma の終射の反転性を合成する。
規約：任意の指定対象に対する全 comma 圏を扱い、単体集合モデルを要求しない。
使われ方：三本矢への共通比較の右射の分解側の全対象の入力。 -/
lemma resolutionCommaTerminal_image_isIso (q : CofibrantResolution (C := C) simplex X)
    (t : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.TrivialFibrationOver X) {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionOverFunctor q) t)))) := by
  let G := MorphismProperty.Over.forget (trivialFibrations C) ⊤ X
  let e := (CostructuredArrow.post (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionOverFunctor q) G t).asEquivalence
  have : IsIso (L.map (nerveMap e.functor)) :=
    inferInstanceAs (IsIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage.imageIso e L hL).hom)
  have : IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionOverFunctor q ⋙ G) (G.obj t))))) :=
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionOverComma_image_isIso q (G.obj t) t.prop L hL
  have h : nerveMap e.functor ≫ SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionOverFunctor q ⋙ G) (G.obj t))) =
      SSet.stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionOverFunctor q) t)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← h, L.map_comp]
  infer_instance

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
