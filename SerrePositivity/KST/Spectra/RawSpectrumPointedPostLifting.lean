module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingAcyclic
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy

/-!
概要：元の点つき全 Hom の後合成へ、指定した部分族を保って全パラメータを持ち上げる。
方針：整合族の全単射 RLP を点つき正方形へ適用し、同じ射影を持つ族の相対比較も行う。
規約：標的は任意の Kan 列。使われ方：符号付き loop の全 Hom 比較の BF 置換への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}} (p : KanSequence.Hom Y Z)
  (hp : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app n).right)
include hp

/-- 元の点つき後合成は、基礎単体集合で全ての単射への RLP を持つ。 -/
lemma pointedPost_rlp :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (pointedPost X p).right :=
  post_rlp X p hp

/-- 指定した部分族と射影を厳密に保つ、元の全 Hom への点つき持ち上げ。 -/
def pointedPostRelativeLift {B A : PointedSimplicialSet.{u}} (j : B ⟶ A) [Mono j.right]
    (a : B ⟶ pointedSpace X Y) (b : A ⟶ pointedSpace X Z)
    (h : a ≫ pointedPost X p = j ≫ b) :
    { l : A ⟶ pointedSpace X Y // j ≫ l = a ∧ l ≫ pointedPost X p = b } :=
  pointedSquareLift j (pointedPost X p) (pointedPost_rlp X p hp) a b h

/-- 任意の点つきパラメータ族を、全段で整合する元の Hom へ持ち上げる。 -/
def pointedPostLift {A : PointedSimplicialSet.{u}} (b : A ⟶ pointedSpace X Z) :
    A ⟶ pointedSpace X Y :=
  (pointedMapLift (pointedPost X p) (pointedPost_rlp X p hp) b).val

/-- 選んだ全パラメータの持ち上げは、元の射影へ戻すと元の族に厳密一致する。 -/
@[reassoc]
lemma pointedPostLift_fac {A : PointedSimplicialSet.{u}} (b : A ⟶ pointedSpace X Z) :
    pointedPostLift X p hp b ≫ pointedPost X p = b :=
  (pointedMapLift (pointedPost X p) (pointedPost_rlp X p hp) b).property

/-- 指定部分の元の垂直ホモトピーを保持して、同じ射影を持つ全 Hom の族を比較する。 -/
lemma pointedPost_homotopy_extension {B A : PointedSimplicialSet.{u}}
    (j : B ⟶ A) [Mono j.right] (f g : A ⟶ pointedSpace X Y)
    (h : f ≫ pointedPost X p = g ≫ pointedPost X p)
    (V : SSet.Homotopy (j.right ≫ f.right) (j.right ≫ g.right))
    (hbase : B.hom ▷ (Δ[1] : SSet.{u}) ≫ V.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (pointedSpace X Y).hom)
    (hvertical : V.h ≫ (pointedPost X p).right =
      fst B.right (Δ[1] : SSet.{u}) ≫ j.right ≫ f.right ≫ (pointedPost X p).right) :
    ∃ H : SSet.Homotopy f.right g.right,
      H.h ≫ (pointedPost X p).right =
        fst A.right (Δ[1] : SSet.{u}) ≫ f.right ≫ (pointedPost X p).right ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h = V.h ∧
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (pointedSpace X Y).hom := by
  obtain ⟨H, hH⟩ := MonoRightLiftingRelativeHomotopy.exists_vertical_homotopy
    (pointedPost X p).right (pointedPost_rlp X p hp) f.right g.right
    (congrArg Under.Hom.right h)
  have hc : V.h ≫ (pointedPost X p).right =
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h ≫ (pointedPost X p).right := by
    rw [hvertical, hH, whiskerRight_fst_assoc]
  obtain ⟨W, hW, hJ⟩ := MonoRightLiftingRelativeHomotopy.exists_extension
    (pointedPost X p).right (pointedPost_rlp X p hp) j.right H V hc
  refine ⟨W, hW.trans hH, hJ, ?_⟩
  rw [← Under.w j, comp_whiskerRight_assoc, hJ, hbase]

/-- 同じ射影を持つ二つの全パラメータ族は、指定部分上で固定した垂直ホモトピーを持つ。 -/
lemma pointedPost_relative_homotopy {B A : PointedSimplicialSet.{u}}
    (j : B ⟶ A) [Mono j.right] (f g : A ⟶ pointedSpace X Y)
    (h : f ≫ pointedPost X p = g ≫ pointedPost X p) (hj : j ≫ f = j ≫ g) :
    ∃ H : SSet.Homotopy f.right g.right,
      H.h ≫ (pointedPost X p).right =
        fst A.right (Δ[1] : SSet.{u}) ≫ f.right ≫ (pointedPost X p).right ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        fst B.right (Δ[1] : SSet.{u}) ≫ j.right ≫ f.right ∧
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (pointedSpace X Y).hom := by
  obtain ⟨H, hH, hJ⟩ :=
    MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy
      (pointedPost X p).right (pointedPost_rlp X p hp) j.right f.right g.right
      (congrArg Under.Hom.right h) (congrArg Under.Hom.right hj)
  refine ⟨H, hH, hJ, ?_⟩
  rw [← Under.w j, comp_whiskerRight_assoc, hJ,
    whiskerRight_fst_assoc, ← Category.assoc B.hom j.right f.right, Under.w j, Under.w f]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
