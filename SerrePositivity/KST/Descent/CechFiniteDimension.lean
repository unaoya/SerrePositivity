module

public import SerrePositivity.KST.Descent.AffineFiniteDimension
public import SerrePositivity.KST.Descent.FiniteTypeCechGeometry
public import SerrePositivity.KST.Descent.AffineSplitDescent

/-!
# 実際のアフィン Čech 各段への有限次元上界の供給

## 概要
局所 Noether 環上の実際の有限型アフィン対象に自然数の次元上界を供給する。

## 方針
アフィン対象の大域切断環に構造射から代数構造を入れ、その有限型性を導出する。
指定された対象の次元は isoSpec の同相で座標環の次元と比較する。

## 規約
有限次元性や座標環の有限型性を追加仮定に残さない。

## 使われ方
論文 補題 3.2 の実際の Čech 各段に対する切断つき降下の次元帰納。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- 概要：有限型アフィン射の始域に有限次元上界を供給する（論文 補題 3.2）。
方針：指定された構造射から大域切断環の有限型代数構造を導く。
規約：基底環の自然数の次元上界以外に、始域の有限次元性を仮定しない。
使われ方：実際の Čech 対象の次元を座標環の上界へ移す。 -/
theorem affineMorphism_dimension_bound {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (d : ℕ) (bound : topologicalKrullDim (Spec (.of A)) ≤ d) :
    ∃ e : ℕ, topologicalKrullDim X ≤ e := by
  let g := X.isoSpec.inv ≫ f
  let φ : A →+* Γ(X, ⊤) := (Spec.preimage g).hom
  let : Algebra A Γ(X, ⊤) := φ.toAlgebra
  have hmap : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ)) := by
    have h : LocallyOfFiniteType g := inferInstance
    exact (Spec.map_preimage g).symm ▸ h
  have hφ : φ.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hmap
  have : Algebra.FiniteType A Γ(X, ⊤) := RingHom.finiteType_algebraMap.mp hφ
  obtain ⟨e, he⟩ := finiteType_spec_dimension_bound (A := A) (T := Γ(X, ⊤)) d bound
  refine ⟨e, ?_⟩
  have dim : topologicalKrullDim X = topologicalKrullDim (Spec Γ(X, ⊤)) :=
    IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph
  exact dim ▸ he

/-- 概要：局所 Noether 基底上の有限型アフィン対象は有限次元（論文 定理 3.1）。
方針：極大イデアルの生成元数の上界を指定構造射へ適用する。
規約：自然数上界を結論として供給する。
使われ方：既存の K0 の局所基底の仮定から次元帰納へ接続する。 -/
theorem localNoether_affineMorphism_dimension_bound [IsLocalRing A]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    ∃ e : ℕ, topologicalKrullDim X ≤ e :=
  affineMorphism_dimension_bound f _ (localNoether_spec_dimension_bound (A := A))

/-- 概要：局所 Noether 基底の実際のアフィン Čech 各段は有限次元（論文 補題 3.2）。
方針：各段のアフィン性と増強射の局所有限型性を導き、基底から上界を供給する。
規約：段ごとの有限次元性や座標環の有限型性を入力しない。
使われ方：切断つき全次数降下の実際の各段への次元帰納。 -/
theorem localNoether_finiteTypeCechStage_dimension_bound [IsLocalRing A]
    {S : Scheme.{u}} [IsNoetherian S] (a : Spec (.of A) ⟶ S)
    [LocallyOfFiniteType a] [QuasiCompact a] {X : FiniteTypeSchemes S}
    [IsAffine X.obj.left] (f : X ⟶ affineOverObject a) (n : SimplexCategoryᵒᵖ) :
    ∃ e : ℕ, topologicalKrullDim ((finiteTypeAugmentedCech f).left.obj n).obj.left ≤ e := by
  have : IsAffine (affineOverObject a).obj.left := inferInstanceAs (IsAffine (Spec (.of A)))
  have hAffine : IsAffine ((finiteTypeAugmentedCech f).left.obj n).obj.left :=
    finiteTypeCechStage_isAffine f n
  have hFinite : LocallyOfFiniteType ((finiteTypeAugmentedCech f).hom.app n).hom.left :=
    finiteTypeMorphism_locallyOfFiniteType _
  exact @localNoether_affineMorphism_dimension_bound A _ _ _
    ((finiteTypeAugmentedCech f).left.obj n).obj.left hAffine
    ((finiteTypeAugmentedCech f).hom.app n).hom.left hFinite

end SerrePositivity.KST.Descent
