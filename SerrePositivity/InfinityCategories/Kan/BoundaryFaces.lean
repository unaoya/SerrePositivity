module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.FibrationBoundary
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
概要：二次元以上の標準単体の境界上の面の貼り合わせ。
方針：余次元一の面と余次元二の交叉の multicoequalizer を使う。
規約：三角形の境界を含み、一次元境界はこの補題では扱わない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。零次数の連結射の単射性。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.BoundaryFaces
end SerrePositivity.KST.Spectra.BoundaryFaces
namespace SerrePositivity.InfinityCategories.Kan.BoundaryFaces
open SerrePositivity.KST.Spectra.BoundaryFaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：標準単体の境界を面とその交叉で表す lattice の貼り合わせ図式。
方針：境界の面による上限表示と面の交叉の式を使う。
規約：単体の次元は n + 2。
使われ方：Goerss–Jardine I §7。境界の全ての面の同時貼り合わせ。 -/
theorem diagram (n : ℕ) :
    Subcomplex.MulticoequalizerDiagram (boundary.{u} (n + 2))
      (fun j : Fin (n + 3) ↦ stdSimplex.face {j}ᶜ)
      (fun j k ↦ stdSimplex.face {j, k}ᶜ) where
  iSup_eq := by rw [boundary_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

/-- 概要：境界の面の貼り合わせ図式の余極限性。
方針：部分複体の lattice の multicoequalizer を単体集合へ移す。
規約：面の添字の線形順序を使う。
使われ方：Goerss–Jardine I §7。互換な面族からの境界射。 -/
noncomputable def isColimit (n : ℕ) :
    IsColimit ((diagram.{u} n).multicofork.toLinearOrder.map Subcomplex.toSSetFunctor) :=
  (diagram n).isColimit'

/-- 概要：全ての面の族の互換性条件。
方針：二つの面の共通の余次元二の面への制限を比較する。
規約：面は Δ[n+1] からの射、貼る境界は ∂Δ[n+2]。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。三角形の境界の貼り合わせ。 -/
def IsCompatible {X : SSet.{u}} {n : ℕ}
    (f : Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ X)) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k

variable {X : SSet.{u}} {n : ℕ} {f : Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ X)}

set_option backward.defeqAttrib.useBackward true in
/-- 概要：互換な面族の multicofork。
方針：各面を標準単体との同型で移し、互換条件を交叉上の等式にする。
規約：二面の交叉の標準同型を使う。
使われ方：Goerss–Jardine I §7。境界の貼り合わせの普遍性。 -/
def multicofork (hf : IsCompatible f) :
    Multicofork ((diagram.{u} n).multispanIndex.toLinearOrder.map Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun j ↦ (stdSimplex.faceSingletonComplIso j).inv ≫ f j) (by
    rintro ⟨⟨a, b⟩, hab⟩
    dsimp
    rw [stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred_assoc _ _ hab,
      stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred_assoc _ _ hab,
      hf a b hab])

/-- 概要：互換な全ての面を境界からの一つの射へ貼り合わせる。
方針：面の貼り合わせの余極限からの射を取る。
規約：n + 2 次元単体の境界。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。全境界充填の入力。 -/
noncomputable def desc (hf : IsCompatible f) : (∂Δ[n + 2] : SSet.{u}) ⟶ X :=
  (isColimit n).desc (multicofork hf)

/-- 概要：貼り合わせた境界射を面に制限すると元の面になる。
方針：余極限の降下の計算則を面の標準同型で移す。
規約：任意の面 j。
使われ方：Goerss–Jardine I §7。充填の境界の検査。 -/
@[reassoc (attr := simp)]
theorem ι_desc (hf : IsCompatible f) (j : Fin (n + 3)) : boundary.ι j ≫ desc hf = f j := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso j).inv]
  simpa only [boundary.faceSingletonComplIso_inv_ι_assoc] using!
    (isColimit.{u} n).fac (multicofork hf) (.right j)

end SerrePositivity.InfinityCategories.Kan.BoundaryFaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.IsCompatible (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.IsCompatible := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.IsCompatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.desc (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.desc := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.desc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.diagram := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.diagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.isColimit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.isColimit := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.isColimit

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.multicofork (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.multicofork := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.multicofork

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.ι_desc := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.ι_desc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.ι_desc_assoc := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.ι_desc_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.IsCompatible._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.IsCompatible._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.IsCompatible._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.IsCompatible._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.IsCompatible._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.IsCompatible._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.desc.congr_simp := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.desc.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryFaces.multicofork._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.multicofork._proof_1
