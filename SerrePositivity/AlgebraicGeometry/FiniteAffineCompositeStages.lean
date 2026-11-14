module

public import SerrePositivity.AlgebraicGeometry.CompositeStageBaseChangeLimit

/-!
概要：極限で affine な有限個の源の底変換模型を、同じ係数段で affine にする。
方針：元の源を保つ実際の極限に Mathlib の 01Z6 を適用し、共通の後段へ移す。
規約：Stacks 01ZN の有限 affine 被覆上の入力。忠実平坦な遷移は要求しない。
使われ方：C04 の affine 性と閉埋め込み性の有限段への降下。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
  [∀ {a b} (f : a ⟶ b), IsAffineHom (D.map f)]
  [∀ a, CompactSpace (D.obj a)] [∀ a, QuasiSeparatedSpace (D.obj a)]
  {S : Scheme.{u}} (γ : D.obj i ⟶ S) (g : c.pt ⟶ S) (h : c.π.app i ≫ γ = g)

include hc h

/-- 実際の極限の源が affine なら、後の底変換模型もある段で affine。 -/
theorem exists_affine_compositeStage_of_isLimit {Y : Scheme.{u}} (p : Y ⟶ S)
    [QuasiCompact p] [QuasiSeparated p] [IsAffine (pullback p g)] :
    ∃ j : Over i, IsAffine (pullback (D.map j.hom ≫ γ) p) := by
  let E := compositeStageBaseChangeDiagram D i γ p
  let e := compositeStageBaseChangeConeWithPoint D c i γ p g h
  have he : IsLimit e := isLimit_compositeStageBaseChangeConeWithPoint D c hc i γ p g h
  haveI : IsAffine e.pt := inferInstanceAs (IsAffine (pullback p g))
  exact Scheme.exists_isAffine_of_isLimit E e he

/-- 有限個の affine な極限の源の底変換模型を、同じ後の段で全て affine にする。 -/
theorem exists_finite_affine_compositeStage_of_isLimit {ι : Type v} [Finite ι]
    (Y : ι → Scheme.{u}) (p : ∀ a, Y a ⟶ S)
    [∀ a, QuasiCompact (p a)] [∀ a, QuasiSeparated (p a)]
    [∀ a, IsAffine (pullback (p a) g)] :
    ∃ j : Over i, ∀ a, IsAffine (pullback (D.map j.hom ≫ γ) (p a)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose j hj using fun a ↦ exists_affine_compositeStage_of_isLimit D c hc i γ g h (p a)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let q (a : ι) : k ⟶ j a := (hk (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)).some
  refine ⟨k, ?_⟩
  intro a
  let E := compositeStageBaseChangeDiagram D i γ (p a)
  letI : IsAffine (E.obj (j a)) := hj a
  have hm : IsAffineHom (E.map (q a)) := by dsimp [E]; infer_instance
  exact @isAffine_of_isAffineHom (E.obj k) (E.obj (j a)) (E.map (q a)) hm (hj a)

end SerrePositivity.AlgebraicGeometry
