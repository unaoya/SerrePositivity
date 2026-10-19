module
public import SerrePositivity.KST.SConstruction.KZeroObjectRecovery
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroSurjectivity
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroNaturality

/-! # 実際の BF 零次 K 群と三角圏 K₀ の同型
概要：元の対象類を保つ比較準同型と逆向き準同型は互いに逆。
方針：対象類の回収と三角圏 K₀ の普遍性で左逆を、全射性で右逆を証明する。
規約：実際の連結 K スペクトルの零次群を使う。
使われ方：L1e の対象類と完全関手に関する自然な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 三角圏 K₀ から BF K 群へ移して戻すと恒等。 -/
lemma kZeroToTriangulatedMap_left_inverse (X : StableModel.{u}) :
    (kZeroToTriangulatedMap X).comp (triangulatedKZeroMap X) = AddMonoidHom.id _ := by
  apply TriangulatedK0.hom_ext
  intro a
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  change kZeroToTriangulatedMap X
    (triangulatedKZeroMap X (TriangulatedK0.mk (SSet.HomotopyCategory.mk x))) = _
  rw [triangulatedKZeroMap_vertex, kZeroToTriangulatedMap_object]
  rfl

/-- BF K 群から三角圏 K₀ へ移して戻しても恒等。 -/
lemma kZeroToTriangulatedMap_right_inverse (X : StableModel.{u}) :
    (triangulatedKZeroMap X).comp (kZeroToTriangulatedMap X) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro b
  obtain ⟨a, rfl⟩ := triangulatedKZeroMap_surjective X b
  have h := DFunLike.congr_fun (kZeroToTriangulatedMap_left_inverse X) a
  exact congrArg (triangulatedKZeroMap X) h

/-- 元の対象類を保つ三角圏 K₀ と実際の BF 零次 K 群の加法群同型。 -/
def triangulatedKZeroEquiv (X : StableModel.{u}) :
    TriangulatedK0 (hoFunctor.obj X.carrier) ≃+
      Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) where
  toFun := triangulatedKZeroMap X
  invFun := kZeroToTriangulatedMap X
  left_inv a := DFunLike.congr_fun (kZeroToTriangulatedMap_left_inverse X) a
  right_inv b := DFunLike.congr_fun (kZeroToTriangulatedMap_right_inverse X) b
  map_add' := (triangulatedKZeroMap X).map_add

/-- 比較同型の対象類の式。 -/
lemma triangulatedKZeroEquiv_vertex (X : StableModel.{u}) (x : X.carrier.obj (Opposite.op ⦋0⦌)) :
    triangulatedKZeroEquiv X (TriangulatedK0.mk (SSet.HomotopyCategory.mk x)) =
      objectKClass X x := triangulatedKZeroMap_vertex X x

/-- 比較同型は完全関手の作用と可換。 -/
lemma triangulatedKZeroEquiv_naturality {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : TriangulatedK0 (hoFunctor.obj X.carrier)) :
    triangulatedKZeroEquiv Y (triangulatedKZeroSourceMap f a) =
      (kHomotopyMap f 0).toAdditive (triangulatedKZeroEquiv X a) :=
  DFunLike.congr_fun (triangulatedKZeroMap_naturality f) a

/-- 逆向き準同型も完全関手の作用と可換。 -/
lemma kZeroToTriangulatedMap_naturality {X Y : StableModel.{u}} (f : X ⟶ Y)
    (b : Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0)) :
    kZeroToTriangulatedMap Y ((kHomotopyMap f 0).toAdditive b) =
      triangulatedKZeroSourceMap f (kZeroToTriangulatedMap X b) := by
  change (triangulatedKZeroEquiv Y).symm ((kHomotopyMap f 0).toAdditive b) =
    triangulatedKZeroSourceMap f ((triangulatedKZeroEquiv X).symm b)
  apply (triangulatedKZeroEquiv Y).injective
  have h := triangulatedKZeroEquiv_naturality f ((triangulatedKZeroEquiv X).symm b)
  simpa only [AddEquiv.apply_symm_apply] using h.symm

end SerrePositivity.KST.SConstruction
