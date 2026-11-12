module
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMappingParameters

public import SerrePositivity.KST.Spectra.PointedMappingNaturality

/-!
概要：任意の単体集合をパラメータとする点つき写像族の curry。
方針：源の基点上の定数性を内部 Hom の等化子条件へ移す。
規約：パラメータ自体に基点は要求しない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。path space の収縮の構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : PointedSimplicialSet.{u}) {A : SSet.{u}}

/-- 概要：パラメータ付き curry はパラメータの前合成と両立する。
方針：等化子への包含後に通常の curry の自然性を使う。
規約：両方の基点条件の証明を明示する。
使われ方：Goerss–Jardine I §7。収縮の端点の評価。 -/
theorem paramCurry_natural {B : SSet.{u}} (g : B ⟶ A)
    (f : X.right ⊗ A ⟶ Y.right)
    (hf : X.hom ▷ A ≫ f = toUnit (𝟙_ SSet.{u} ⊗ A) ≫ Y.hom)
    (hg : X.hom ▷ B ≫ (X.right ◁ g ≫ f) = toUnit (𝟙_ SSet.{u} ⊗ B) ≫ Y.hom) :
    g ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y f hf = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y (X.right ◁ g ≫ f) hg := by
  apply (cancel_mono (PointedObject.basedHomι X Y)).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, MonoidalClosed.curry_natural_left]

/-- 概要：点つき内部 Hom の評価はパラメータが定数写像なら基点で定数。
方針：内部 Hom の基点を包含して通常の curry を uncurry する。
規約：ここでのパラメータの基点は定数写像。
使われ方：Goerss–Jardine I §7。定数 path が収縮中に固定されること。 -/
theorem uncurry_parameter_basepoint :
    X.right ◁ (PointedObject.basedHom X Y).hom ≫
      MonoidalClosed.uncurry (PointedObject.basedHomι X Y) =
        toUnit (X.right ⊗ 𝟙_ SSet.{u}) ≫ Y.hom := by
  rw [← MonoidalClosed.uncurry_natural_left, PointedObject.basedHom_basepoint_ι,
    PointedObject.homBasepoint, MonoidalClosed.uncurry_curry]

/-- 概要：常に基点を値とする写像族の curry は定数写像のパラメータ族。
方針：等化子への包含後に定数写像の curry を計算する。
規約：基点条件の証明は任意。
使われ方：Goerss–Jardine I §7。path space の収縮の初端。 -/
theorem paramCurry_constant
    (hf : X.hom ▷ A ≫ (toUnit (X.right ⊗ A) ≫ Y.hom) =
      toUnit (𝟙_ SSet.{u} ⊗ A) ≫ Y.hom) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y (toUnit (X.right ⊗ A) ≫ Y.hom) hf =
      toUnit A ≫ (PointedObject.basedHom X Y).hom := by
  apply (cancel_mono (PointedObject.basedHomι X Y)).mp
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, Category.assoc, PointedObject.basedHom_basepoint_ι,
    PointedObject.curry_constant]
  rfl

end

end SerrePositivity.KST.Spectra.PointedMapping
