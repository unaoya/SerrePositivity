module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：交代余面複体の構成と加法関手の適用の可換性。
方針：各複体次数の恒等同型を使い、微分の有限和と整数倍の保存を適用する。
規約：通常の加法圏の複体の自然同型。
使われ方：Goerss–Jardine VIII §2。線形 cochain の加法群への忘却と π_* の複体の比較。
-/

@[expose] public section

open CategoryTheory

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

@[simp]
lemma alternatingCoface_obj_d (X : CosimplicialObject C) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD X n := by
  simp [AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]

@[simp]
lemma alternatingCoface_map_f {X Y : CosimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex C).map f).f n =
      f.app (SimplexCategory.mk n) := rfl

attribute [local simp] Functor.map_zsmul in
/-- 概要：交代余面複体の後で加法関手を適用する操作と先に係数へ適用する操作は自然に同型。
方針：各次数の恒等同型を有限交代和の保存で複体の同型へ束ねる。
規約：添字の複体は自然数で上向き。
使われ方：Goerss–Jardine VIII §2。加法群への忘却と線形 cochain 比較の交換。 -/
def alternatingCofaceFunctorIso (F : C ⥤ D) [F.Additive] :
    AlgebraicTopology.alternatingCofaceMapComplex C ⋙ F.mapHomologicalComplex _ ≅
      (CosimplicialObject.whiskering C D).obj F ⋙
        AlgebraicTopology.alternatingCofaceMapComplex D :=
  NatIso.ofComponents
    (fun _ ↦ HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _))

end

end SerrePositivity.KST.Spectra
