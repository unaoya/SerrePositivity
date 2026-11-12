module

public import SerrePositivity.KST.Spectra.PointedMappingFamilyVertices
public import SerrePositivity.KST.Spectra.SpectrumMorphisms

/-!
概要：通常のパラメータ族による写像空間の頂点と点つき閉構造による頂点の一致。
方針：非基点側の単位の評価を計算し、二つの curry を等化子への包含後に比較する。
規約：標的の Kan 性は不要。
使われ方：BF 1978 §2、HTT A.3.3、Goerss–Jardine I §7。suspension によるホモトピーの保存。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき閉構造の curry は smash の商からの具体的な curry。
方針：閉構造に採用された随伴の Hom 同値を開く。
規約：点つき単体集合の閉構造。
使われ方：BF 1978 §2、HTT A.3.3。頂点の二つの表示の比較。 -/
theorem curry_eq_smashCurry {X Y Z : PointedSimplicialSet.{u}} (f : X ⊗ Y ⟶ Z) :
    MonoidalClosed.curry f = PointedObject.smashCurry f := by
  change (PointedObject.smashHomAdjunction X).homEquiv Y Z f = _
  simp only [PointedObject.smashHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- 概要：非基点側の単位と smash の右単位の評価は通常の右単位子。
方針：smash の交換と左単位の非基点側の式を使う。
規約：最初の inl は零次球面の非基点側。
使われ方：BF 1978 §2、Goerss–Jardine I §7。通常のパラメータ族の零次評価。 -/
@[reassoc]
theorem nonbasepoint_right_unit (X : PointedSimplicialSet.{u}) :
    X.right ◁ (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ PointedSimplicialSet.{u}).right) ≫
      (PointedObject.smashQuotient X (𝟙_ PointedSimplicialSet.{u})).right ≫
        (ρ_ X).hom.right = (ρ_ X.right).hom := by
  have hq : (PointedObject.smashQuotient X (𝟙_ PointedSimplicialSet.{u})).right ≫
      (ρ_ X).hom.right =
    (PointedObject.prodSwap X (𝟙_ PointedSimplicialSet.{u})).right ≫
      PointedObject.leftUnitRaw X := by
    change (PointedObject.smashQuotient X PointedObject.sphereZero).right ≫
      ((PointedObject.smashSwap X PointedObject.sphereZero).right ≫
        (PointedObject.leftUnitHom X).right) = _
    rw [← Category.assoc, ← Under.comp_right, PointedObject.smashQuotient_swap,
      Under.comp_right, Category.assoc, ← Under.comp_right,
      PointedObject.smashQuotient_leftUnitHom]
    rfl
  erw [hq]
  have hs : X.right ◁ (coprod.inl : 𝟙_ SSet.{u} ⟶
      (𝟙_ PointedSimplicialSet.{u}).right) ≫
      (PointedObject.prodSwap X (𝟙_ PointedSimplicialSet.{u})).right =
    (β_ X.right (𝟙_ SSet.{u})).hom ≫ coprod.inl ▷ X.right := rfl
  rw [← Category.assoc, hs, Category.assoc, PointedObject.leftUnitRaw_first]
  rfl

/-- 概要：パラメータ族の点の射は閉構造の単位の非基点側の制限と一致する。
方針：等化子へ含め、curry の自然性と単位の評価を比較する。
規約：Kan 性を要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。写像空間の頂点表示の一致。 -/
theorem pointFamily_closed {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointFamily f = PointedSimplicialSet.deltaZeroUnitIso.hom ≫
      PointedSimplicialSet.unitUnderlyingHom (PointedObject.basedHom X Y)
        (MonoidalClosed.curry' f) := by
  apply (cancel_mono (PointedObject.basedHomι X Y)).mp
  rw [pointFamily, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι]
  dsimp only [PointedSimplicialSet.unitUnderlyingHom, PointedObject.adjoinHomEquiv,
    Equiv.coe_fn_mk, MonoidalClosed.curry']
  rw [curry_eq_smashCurry, Category.assoc, Category.assoc, PointedObject.smashCurry_ι]
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left]
  congr 1
  simp only [Under.comp_right]
  erw [nonbasepoint_right_unit_assoc]
  rfl

end

end SerrePositivity.KST.Spectra.PointedMapping
