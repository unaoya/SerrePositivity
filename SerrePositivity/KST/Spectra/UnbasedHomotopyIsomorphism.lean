module

public import SerrePositivity.KST.Spectra.UnpointedPathEvaluation

/-!
概要：基点を固定しないホモトピーは全基点 π_* 同型性を保存する。
方針：ホモトピーを指数 path への射へ転置し、二つの端点の同型性を打ち消す。
規約：類の写像の等式は主張せず、異なる終点基点での全単射性を比較する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）、BF 1978 §2。一般の Kan 射の Whitehead。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.KanPath

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：指数 path の curry を端点で評価する一般計算式。
方針：指数の制限と curry の可換性を単位の評価へ合成する。
規約：h のテンソルの第一成分が区間。
使われ方：Goerss–Jardine I §7。ホモトピーの転置の端点の照合。 -/
theorem curry_evaluation {A X : SSet.{u}} (h : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (t : Fin 2) :
    MonoidalClosed.curry h ≫ evaluation X t = (λ_ A).inv ≫ endpoint t ▷ A ≫ h := by
  rw [evaluation, ← Category.assoc, curry_pre_app, curry_unit_evaluation]

/-- 概要：基点を固定しないホモトピーの指数 path 対象への転置。
方針：区間をテンソルの第一成分へ交換して curry する。
規約：基点の移動を実際の path の頂点として保持する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）。π_* 同型性のホモトピー不変性。 -/
def transpose {A X : SSet.{u}} {f g : A ⟶ X} (H : SSet.Homotopy f g) : A ⟶ object X :=
  MonoidalClosed.curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h)

/-- 概要：ホモトピーの転置を時刻零で評価すると元の始点射。
方針：単位からの端点挿入とテンソル交換を区間の始点包含へ同定する。
規約：通常の単体集合の射の等式。
使われ方：Goerss–Jardine I §7。始点の π_* 同型性の打ち消し。 -/
@[reassoc (attr := simp)]
theorem transpose_zero {A X : SSet.{u}} {f g : A ⟶ X} (H : SSet.Homotopy f g) :
    transpose H ≫ evaluation X 0 = f := by
  rw [transpose, curry_evaluation]
  have h : (λ_ A).inv ≫ endpoint.{u} 0 ▷ A ≫ (β_ (Δ[1] : SSet.{u}) A).hom = SSet.ι₀ := rfl
  calc
    _ = SSet.ι₀ ≫ H.h := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ H.h) h
    _ = f := H.h₀

/-- 概要：ホモトピーの転置を時刻一で評価すると元の終点射。
方針：端点挿入とテンソル交換を区間の終点包含へ同定する。
規約：基点を固定する仮定はない。
使われ方：Goerss–Jardine I §7。終点の π_* 同型性の打ち消し。 -/
@[reassoc (attr := simp)]
theorem transpose_one {A X : SSet.{u}} {f g : A ⟶ X} (H : SSet.Homotopy f g) :
    transpose H ≫ evaluation X 1 = g := by
  rw [transpose, curry_evaluation]
  have h : (λ_ A).inv ≫ endpoint.{u} 1 ▷ A ≫ (β_ (Δ[1] : SSet.{u}) A).hom = SSet.ι₁ := rfl
  calc
    _ = SSet.ι₁ ≫ H.h := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ H.h) h
    _ = g := H.h₁

end

end SerrePositivity.KST.Spectra.KanPath

namespace SerrePositivity.KST.Spectra

/-- 概要：Kan 複体間の一般の区間ホモトピーは全基点 π_* 同型性を保存する。
方針：path 対象への転置の後で全単射な二つの端点をそれぞれ打ち消す。
規約：基点の固定は不要。零次数を含む。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）、BF 1978 §2。mapping path の比較。 -/
theorem kanPiIsomorphism_iff_of_homotopy {A X : SSet.{u}} [KanComplex A] [KanComplex X]
    {f g : A ⟶ X} (H : SSet.Homotopy f g) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f ↔ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g := by
  constructor
  · intro hf
    have hzero : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (KanPath.transpose H ≫ KanPath.evaluation X 0) := by
      rw [KanPath.transpose_zero]
      exact hf
    have ht := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hzero (KanPath.evaluation_piIsomorphism X 0)
    have h := ht.comp (KanPath.evaluation_piIsomorphism X 1)
    rw [KanPath.transpose_one] at h
    exact h
  · intro hg
    have hone : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (KanPath.transpose H ≫ KanPath.evaluation X 1) := by
      rw [KanPath.transpose_one]
      exact hg
    have ht := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hone (KanPath.evaluation_piIsomorphism X 1)
    have h := ht.comp (KanPath.evaluation_piIsomorphism X 0)
    rw [KanPath.transpose_zero] at h
    exact h

end SerrePositivity.KST.Spectra
