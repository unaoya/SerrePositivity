module

public import SerrePositivity.AlgebraicGeometry.IntegerModelAbsoluteFinitePresentation
public import SerrePositivity.AlgebraicGeometry.StageModelOverLimit
public import Mathlib.AlgebraicGeometry.SpreadingOut

/-!
概要：固定の有限型整数模型への射を、実際の係数模型の有限段へ因子化する。
方針：元の対象を頂点に保つ極限と、終対象上の局所有限表示性を使う。
規約：元の射との指定された等式を返し、忠実平坦性は要求しない。
使われ方：B02・B03 の固定の平坦模型への β の有限段への移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 固定の有限型整数模型への射は、実際の係数模型のある有限段を通る。 -/
theorem exists_integerModel_stage_factor
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (i : J) {T T₀ Y : Scheme.{u}} (a : T ⟶ T₀) (x : T ⟶ c.pt)
    (r : T₀ ⟶ D.obj i) [QuasiCompact r] [QuasiSeparated r]
    (hpb : IsPullback a x r (c.π.app i))
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (p : Y ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation p] (β : T ⟶ Y) :
    ∃ (j : Over i) (b : (stageBaseChangeDiagram D i r).obj j ⟶ Y),
      (stageModelCone D c i a x r hpb).π.app j ≫ b = β := by
  let B := stageBaseChangeDiagram D i r
  let C := stageModelCone D c i a x r hpb
  have hC : IsLimit C := isLimit_stageModelCone D c hc i a x r hpb
  haveI {j k : Over i} (g : j ⟶ k) : IsAffineHom (B.map g) := by
    dsimp [B]
    infer_instance
  haveI (j : Over i) : CompactSpace (B.obj j) := inferInstanceAs
    (CompactSpace ((stageBaseChangeDiagram D i r).obj j))
  haveI (j : Over i) : QuasiSeparatedSpace (B.obj j) := inferInstanceAs
    (QuasiSeparatedSpace ((stageBaseChangeDiagram D i r).obj j))
  haveI : LocallyOfFinitePresentation (terminal.from Y) :=
    locallyOfFinitePresentation_to_terminal_of_integer_model A p
  let t : B ⟶ (Functor.const (Over i)).obj (⊤_ Scheme.{u}) := {
    app j := terminal.from (B.obj j)
    naturality := by
      intro j k g
      change B.map g ≫ terminal.from (B.obj k) = terminal.from (B.obj j) ≫ 𝟙 _
      simp }
  have ht : C.π ≫ t = (Functor.const (Over i)).map (β ≫ terminal.from Y) := by
    ext j
    change C.π.app j ≫ terminal.from (B.obj j) = β ≫ terminal.from Y
    apply terminalIsTerminal.hom_ext
  obtain ⟨j, b, hb, _⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    B t (terminal.from Y) C hC β ht
  exact ⟨j, b, hb⟩

end SerrePositivity.AlgebraicGeometry
