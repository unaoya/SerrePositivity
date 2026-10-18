module

public import SerrePositivity.KST.Descent.CechFiniteDimension
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# 一般の有限型対象の有限次元上界

## 概要
準コンパクトな有限型スキームに、アフィン性を要求せず自然数の次元上界を供給する。

## 方針
開埋め込みによる点の coheight の保存と有限アフィン被覆を使う。

## 規約
基底 Noether 環の有限次元性は明示する。局所 Noether 基底では高さ定理から供給する。

## 使われ方
論文 補題 3.3 と定理 3.1 の blowup を含む一般の底変換の次元帰納。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

namespace SerrePositivity.KST.Descent

attribute [local instance] specializationOrder

/-- 概要：開被覆上の共通次元上界は全体の次元上界になる（論文 補題 3.3）。
方針：sober 空間の点と既約閉集合の順序同型、開埋め込みの coheight 保存を使う。
規約：被覆の有限性は不要。使われ方：有限アフィン被覆で得た最大上界を貼り合わせる。 -/
theorem openCover_dimension_le {X : Scheme.{u}} (U : X.OpenCover) (d : ℕ)
    (bound : ∀ i, topologicalKrullDim (U.X i) ≤ d) : topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim, krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨y, hy⟩ := U.covers x
  have h := (U.f (U.idx x)).isOpenEmbedding.coheight_eq (x := y) (U.f (U.idx x))
  rw [hy] at h
  have localBound : (coheight y : WithBot ℕ∞) ≤ d := by
    calc
      (coheight y : WithBot ℕ∞) ≤ krullDim (U.X (U.idx x)) := coheight_le_krullDim y
      _ = topologicalKrullDim (U.X (U.idx x)) :=
        (krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := U.X (U.idx x)))).symm
      _ ≤ d := bound _
  exact (congrArg (fun a : ℕ∞ ↦ (a : WithBot ℕ∞)) h) ▸ localBound

/-- 概要：有限開被覆の各対象が有限次元なら全体も有限次元（論文 補題 3.3）。
方針：各自然数上界の有限最大値を取り、共通上界の貼り合わせを適用する。
規約：空スキームと空被覆も含む。使われ方：有限アフィン被覆への還元。 -/
theorem finiteOpenCover_dimension_bound {X : Scheme.{u}} (U : X.OpenCover) [Finite U.I₀]
    (bound : ∀ i, ∃ d : ℕ, topologicalKrullDim (U.X i) ≤ d) :
    ∃ d : ℕ, topologicalKrullDim X ≤ d := by
  classical
  let := Fintype.ofFinite U.I₀
  choose e he using bound
  refine ⟨Finset.univ.sup e, openCover_dimension_le U _ fun i ↦ (he i).trans ?_⟩
  exact_mod_cast (Finset.le_sup (f := e) (Finset.mem_univ i))

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- 概要：準コンパクトな有限型射の始域はアフィン性なしに有限次元（定理 3.1）。
方針：有限アフィン部分被覆の各構造射にアフィン次元上界を適用し、最大値を貼る。
規約：有限次元の基底 Noether 環を明示する。
使われ方：blowup を含む一般の有限型対象への次元帰納。 -/
theorem schemeMorphism_dimension_bound {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (d : ℕ) (bound : topologicalKrullDim (Spec (.of A)) ≤ d) :
    ∃ e : ℕ, topologicalKrullDim X ≤ e := by
  let U := X.affineCover.finiteSubcover
  apply finiteOpenCover_dimension_bound U
  intro i
  have : IsAffine (U.X i) := by
    dsimp [U, Scheme.OpenCover.finiteSubcover]
    infer_instance
  exact affineMorphism_dimension_bound (U.f i ≫ f) d bound

/-- 概要：局所 Noether 基底上の準コンパクトな有限型スキームは有限次元（定理 3.1）。
方針：高さ定理から得た基底の上界を一般のスキーム射へ適用する。
規約：始域のアフィン性と次元上界を追加仮定にしない。
使われ方：一般の底変換・blowup の各 Čech 段の次元帰納。 -/
theorem localNoether_schemeMorphism_dimension_bound [IsLocalRing A]
    {X : Scheme.{u}} [CompactSpace X] (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    ∃ e : ℕ, topologicalKrullDim X ≤ e :=
  schemeMorphism_dimension_bound f _ (localNoether_spec_dimension_bound (A := A))

/-- 概要：局所 Noether 基底上の実際の一般の Čech 各段は有限次元（補題 3.2・3.3）。
方針：有限型の圏内での Noether 性から準コンパクト性を得て、指定増強射へ上界を適用する。
規約：始域のアフィン性や段ごとの有限次元性を仮定しない。
使われ方：blowup を含む混合 Čech の各段への次元帰納。 -/
theorem localNoether_generalCechStage_dimension_bound [IsLocalRing A]
    {S : Scheme.{u}} [IsNoetherian S] (a : Spec (.of A) ⟶ S)
    [LocallyOfFiniteType a] [QuasiCompact a] {X : FiniteTypeSchemes S}
    (f : X ⟶ affineOverObject a) (n : SimplexCategoryᵒᵖ) :
    ∃ e : ℕ, topologicalKrullDim ((finiteTypeAugmentedCech f).left.obj n).obj.left ≤ e := by
  have hFinite : LocallyOfFiniteType ((finiteTypeAugmentedCech f).hom.app n).hom.left :=
    finiteTypeMorphism_locallyOfFiniteType _
  exact @localNoether_schemeMorphism_dimension_bound A _ _ _
    ((finiteTypeAugmentedCech f).left.obj n).obj.left inferInstance
    ((finiteTypeAugmentedCech f).hom.app n).hom.left hFinite

end SerrePositivity.KST.Descent
