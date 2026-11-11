module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# 単体集合の宇宙の持ち上げと Kan 性

概要：宇宙を持ち上げた単体集合が Kan なら元も Kan である。
方針：米田対応で面の族を持ち上げ、充填単体の ULift を外す。
規約：対象の宇宙と係数環の宇宙を同一視しない。
使われ方：HA 1.3.1.12–1.3.1.14、Kerodon 2.5.6（Tag 00QQ） の小さい Dold–Kan Hom の構成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

universe v u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：標準単体からの写像をより大きい宇宙へ持ち上げる。
方針：米田対応の単体を ULift に入れ、逆の米田対応を使う。
規約：標準単体自体の宇宙も同時に変える。
使われ方：HA 1.3.1.14 の Kan 性を宇宙の制約なしに利用する準備。 -/
def uliftSimplexHom {X : SSet.{u}} {n : ℕ} (f : (Δ[n] : SSet.{u}) ⟶ X) :
    (Δ[n] : SSet.{max u v}) ⟶ SSet.uliftFunctor.{v, u}.obj X :=
  SSet.yonedaEquiv.symm ⟨SSet.yonedaEquiv f⟩

/-- 概要：標準単体からの持ち上げた写像の米田対応は元の単体の持ち上げである。
方針：米田対応とその逆の相殺を使う。
規約：両方の宇宙を保持する。
使われ方：HA 1.3.1.14 のホーン面と充填単体の移送の計算。 -/
lemma uliftSimplexHom_yonedaEquiv {X : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ X) :
    SSet.yonedaEquiv (uliftSimplexHom.{v} f) = ULift.up (SSet.yonedaEquiv f) :=
  SSet.yonedaEquiv.apply_symm_apply _

/-- 概要：標準単体からの写像の宇宙の持ち上げは面への制限と可換である。
方針：米田対応を適用し、持ち上げた単体の面を計算する。
規約：全ての面番号を扱う。
使われ方：HA 1.3.1.14 の Kan 充填を宇宙の間で移す際の面の整合性。 -/
lemma uliftSimplexHom_face {X : SSet.{u}} {n : ℕ} (f : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (j : Fin (n + 2)) :
    SSet.stdSimplex.δ j ≫ uliftSimplexHom.{v} f =
      uliftSimplexHom.{v} (SSet.stdSimplex.δ j ≫ f) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, uliftSimplexHom_yonedaEquiv,
    uliftSimplexHom_yonedaEquiv, SSet.stdSimplex.yonedaEquiv_δ_comp]
  rfl

/-- 概要：宇宙の持ち上げが Kan 性を反映する。
方針：互換なホーン面の族を持ち上げて充填し、充填単体の down を取る。
規約：一般の単体的群の Kan 性を仮定しない。
使われ方：HA 1.3.1.14、Kerodon 2.5.6（Tag 00QQ） の小さい Hom 模型の Kan 性。 -/
lemma kanComplex_of_ulift (X : SSet.{u})
    [SSet.KanComplex (SSet.uliftFunctor.{v, u}.obj X)] : SSet.KanComplex X := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  have hF : SSet.horn.IsCompatible (fun j hj ↦ uliftSimplexHom.{v} (f j hj)) := by
    cases n with
    | zero => trivial
    | succ n =>
      intro j k hj hk hjk
      rw [uliftSimplexHom_face, uliftSimplexHom_face, hf j k hj hk hjk]
  obtain ⟨φ, hφ⟩ := hF.exists_lift_of_kanComplex
  refine ⟨SSet.yonedaEquiv.symm (SSet.yonedaEquiv φ).down, fun j hj ↦ ?_⟩
  apply SSet.yonedaEquiv.injective
  have h := congrArg (fun g : (Δ[n] : SSet.{max u v}) ⟶
      SSet.uliftFunctor.{v, u}.obj X ↦ (SSet.yonedaEquiv g).down) (hφ j hj)
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, uliftSimplexHom_yonedaEquiv] at h
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
  exact h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
