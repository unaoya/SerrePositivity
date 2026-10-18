module

public import SerrePositivity.KST.Descent.TensorBaseChangeAction
public import SerrePositivity.KST.Descent.AffineOrbitCovering
public import SerrePositivity.KST.Descent.ReducedSourceDescent
public import Mathlib.RingTheory.FiniteStability

/-!
# 幾何的推移性の係数拡大

## 概要
既存の幾何的推移性を任意の A 代数 B への係数拡大に移す。

## 方針
幾何ファイバーのテンソル積の標準同型と群作用の両立を証明し、素イデアルを移す。

## 規約
B を左因子とする標準の B 代数構造と構成済みの群作用を使う。

## 使われ方
論文 補題 3.2・3.3・定理 3.1 の基底変更と閉中心上への帰納。
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace SerrePositivity.KST.Descent

variable {A B T G : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

/-- 概要：基底変更後の幾何ファイバーの標準同型（論文 定理 3.1）。
方針：外側の因子を交換し、係数拡大を打ち消して、再び因子を交換する。
規約：A 代数の同型として指定する。
使われ方：係数拡大後の幾何的推移性。 -/
noncomputable def tensorBaseChangeFiberEquiv (Ω : Type u) [CommRing Ω]
    [Algebra B Ω] [Algebra A Ω] [IsScalarTower A B Ω] :
    ((B ⊗[A] T) ⊗[B] Ω) ≃ₐ[A] T ⊗[A] Ω :=
  ((Algebra.TensorProduct.comm B (B ⊗[A] T) Ω).restrictScalars A).trans
    (((Algebra.TensorProduct.cancelBaseChange A B B Ω T).restrictScalars A).trans
      (Algebra.TensorProduct.comm A Ω T))

/-- 概要：幾何ファイバーの標準同型の純テンソル上の公式（論文 §3）。
方針：交換と係数拡大の打ち消しの公式を合成する。
規約：B の元は Ω のスカラーとして作用する。
使われ方：標準同型と群作用の可換性。 -/
@[simp] theorem tensorBaseChangeFiberEquiv_tmul (Ω : Type u) [CommRing Ω]
    [Algebra B Ω] [Algebra A Ω] [IsScalarTower A B Ω] (b : B) (t : T) (ω : Ω) :
    tensorBaseChangeFiberEquiv (A := A) (B := B) Ω ((b ⊗ₜ[A] t) ⊗ₜ[B] ω) =
      t ⊗ₜ[A] (b • ω) := by
  simp [tensorBaseChangeFiberEquiv]

/-- 概要：幾何ファイバーの標準同型は指定群作用と可換（論文 定理 3.1）。
方針：二重の純テンソルで等式を検査する。
規約：左側は B に関する既存の tensorAction、右側は A に関する tensorAction。
使われ方：素イデアルの推移性を同型で移す。 -/
theorem tensorBaseChangeFiberEquiv_equivariant (Ω : Type u) [CommRing Ω]
    [Algebra B Ω] [Algebra A Ω] [IsScalarTower A B Ω] (g : G)
    (z : (B ⊗[A] T) ⊗[B] Ω) :
    tensorBaseChangeFiberEquiv (A := A) (B := B) Ω (tensorAction B (B ⊗[A] T) G Ω g z) =
      tensorAction A T G Ω g (tensorBaseChangeFiberEquiv (A := A) (B := B) Ω z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x ω =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
    | tmul b t => simp [tensorAction]

/-- 概要：既存の幾何的推移性は任意の係数拡大で保存される（論文 定理 3.1）。
方針：幾何ファイバーの同変な標準同型で素イデアルを往復させる。
規約：B の有限型性・平坦性は不要。構成済みの B 線形な作用を使う。
使われ方：有限忠実平坦な Čech の各項と閉中心上の帰納への推移性の移行。 -/
theorem geometricTransitivity_baseChange (transitive : IsGeometricallyTransitive A T G) :
    IsGeometricallyTransitive B (B ⊗[A] T) G := by
  intro Ω _ _ _
  let : Algebra A Ω := ((algebraMap B Ω).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B Ω := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  intro x y
  let e := tensorBaseChangeFiberEquiv (A := A) (B := B) (T := T) Ω
  obtain ⟨g, hg⟩ := transitive Ω
    (PrimeSpectrum.comap e.symm.toRingEquiv.toRingHom x)
    (PrimeSpectrum.comap e.symm.toRingEquiv.toRingHom y)
  refine ⟨g, ?_⟩
  have comm : (tensorAction B (B ⊗[A] T) G Ω g).toRingHom.comp e.symm.toRingEquiv.toRingHom =
      e.symm.toRingEquiv.toRingHom.comp (tensorAction A T G Ω g).toRingHom := by
    apply RingHom.ext
    intro z
    change tensorAction B (B ⊗[A] T) G Ω g (e.symm z) =
      e.symm (tensorAction A T G Ω g z)
    apply e.injective
    rw [e.apply_symm_apply]
    exact (tensorBaseChangeFiberEquiv_equivariant Ω g (e.symm z)).trans
      (congrArg (tensorAction A T G Ω g) (e.apply_symm_apply z))
  apply PrimeSpectrum.comap_injective_of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective
  change PrimeSpectrum.comap
      ((tensorAction B (B ⊗[A] T) G Ω g).toRingHom.comp e.symm.toRingEquiv.toRingHom) x =
    PrimeSpectrum.comap e.symm.toRingEquiv.toRingHom y
  rw [comm]
  exact hg

/-- 概要：任意のアフィン基底変更後にも移動切断が全体を覆う（論文 定理 3.1）。
方針：幾何的推移性の係数拡大を、有限型アフィン対象の被覆定理に適用する。
規約：変更後の切断の存在を入力し、被覆や推移性を追加仮定にしない。
使われ方：Čech の各項およびアフィン閉中心上の実際の軌道正方形。 -/
theorem affine_baseChange_translatedSection_covering [Algebra.FiniteType A T]
    (transitive : IsGeometricallyTransitive A T G)
    (s : affineBaseObject B ⟶ affineAlgebraObject B (B ⊗[A] T))
    (hs : s ≫ affineAlgebraProjection B (B ⊗[A] T) = 𝟙 (affineBaseObject B)) :
    ⋃ t : TranslatedSectionIndex (affineAlgebraAction (G := G) B (B ⊗[A] T)) s,
      Set.range t.val.hom.left = Set.univ :=
  affine_translatedSection_covering B (B ⊗[A] T) (geometricTransitivity_baseChange transitive) s hs

/-- 概要：基底変更後に始域を被約化しても移動切断が全体を覆う（論文 定理 3.1）。
方針：基底変更後の点の推移性を被約化の包含で移し、切断の被覆判定を適用する。
規約：基底 Spec B は固定し、被約化した始域への切断の存在を入力する。
使われ方：被約な閉中心上への次元帰納で用いる実際の被覆条件。 -/
theorem affine_baseChange_reducedSource_covering [Algebra.FiniteType A T]
    (transitive : IsGeometricallyTransitive A T G)
    (s : affineBaseObject B ⟶ finiteTypeReduction (affineAlgebraObject B (B ⊗[A] T)))
    (hs : s ≫ (finiteTypeReductionInclusion (affineAlgebraObject B (B ⊗[A] T)) ≫
      affineAlgebraProjection B (B ⊗[A] T)) = 𝟙 (affineBaseObject B)) :
    ⋃ t : TranslatedSectionIndex
        (finiteTypeReductionAction (affineAlgebraAction (G := G) B (B ⊗[A] T))) s,
      Set.range t.val.hom.left = Set.univ := by
  apply translatedSection_covering
    (finiteTypeReductionInclusion (affineAlgebraObject B (B ⊗[A] T)) ≫
      affineAlgebraProjection B (B ⊗[A] T)) s hs
    (finiteTypeReductionAction (affineAlgebraAction B (B ⊗[A] T)))
  apply reducedSourceAction_transitive_on_fibers
  intro x y hxy
  exact specAction_transitive_on_fibers (geometricTransitivity_baseChange transitive) x y hxy

/-- 概要：被約な基底上の元の切断を被約化へ移し、その移動で被覆する（定理 3.1）。
方針：有限型の圏内の被約化への持ち上げを構成し、合成公式から切断性を導く。
規約：被約化後の切断を追加仮定にせず、指定された元の切断から構成する。
使われ方：被約な閉中心上への帰納に必要な、被約な始域の軌道被覆。 -/
theorem affine_baseChange_liftedSection_covering [Algebra.FiniteType A T]
    [AlgebraicGeometry.IsReduced (affineBaseObject B).obj.left]
    (transitive : IsGeometricallyTransitive A T G)
    (s : affineBaseObject B ⟶ affineAlgebraObject B (B ⊗[A] T))
    (hs : s ≫ affineAlgebraProjection B (B ⊗[A] T) = 𝟙 (affineBaseObject B)) :
    ⋃ t : TranslatedSectionIndex
        (finiteTypeReductionAction (affineAlgebraAction (G := G) B (B ⊗[A] T)))
        (finiteTypeReductionLift s), Set.range t.val.hom.left = Set.univ := by
  apply affine_baseChange_reducedSource_covering transitive (finiteTypeReductionLift s)
  rw [← Category.assoc, finiteTypeReductionLift_comp_inclusion, hs]

end SerrePositivity.KST.Descent
