module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfFullyFaithful
/-!
概要：指定生成集合の全シフト間の Hom 比較をその thick 閉包へ延長する。
方針：相対 Hom 比較の cone 二対三と retract 閉性で両変数の厚い帰納を行う。
規約：生成集合を入力に保持し、既存の全代表版を変更しない。
使われ方：D-17 の実 dg 関手に対する自由代表からの生成判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite
open scoped CategoryTheory.Pretriangulated.Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma criterionPerf_hom_bijective_of_generators
    (F : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Additive] (G : Set D)
    (hgen : ∀ (d : D), d ∈ G → ∀ (d' : D), d' ∈ G → ∀ (m n : ℤ),
      Function.Bijective (F.map (X := (criterionPerfRepresentable A D d)⟦m⟧)
        (Y := (criterionPerfRepresentable A D d')⟦n⟧)))
    (X : DerivedModuleCategory A D) (hX : modulePerfectOver A D G X)
    (Y : DerivedModuleCategory A D) (hY : modulePerfectOver A D G Y) :
    Function.Bijective (F.map (X := X) (Y := Y)) := by
  let S₀ : ObjectProperty (DerivedModuleCategory A D) :=
    fun Z => ∃ d ∈ G, Z = criterionPerfRepresentable A D d
  let S := S₀.shiftClosure ℤ
  let P := criterionPerfRelativeHomTargets F S
  have htarget : modulePerfectOver A D G ≤ P := by
    apply (modulePerfectOver_le_iff_generators A D P G).2
    intro d' hd' Z hZ
    obtain ⟨Z', m, e, d, hd, rfl⟩ := hZ
    exact homComparison_bijective_of_iso F e.symm
      ((shiftFunctorZero (DerivedModuleCategory A D) ℤ).app _)
      (hgen d hd d' hd' m 0)
  let Q := criterionPerfRelativeHomTargets F.op (modulePerfectOver A D G).op
  let : Q.unop.IsStableUnderRetracts := ⟨fun a ha => Q.prop_of_retract a.op ha⟩
  have hsource : modulePerfectOver A D G ≤ Q.unop := by
    apply (modulePerfectOver_le_iff_generators A D Q.unop G).2
    intro d hd Z hZ
    apply (criterionPerfHomComparison_op_iff F _ _).2
    exact htarget Z.unop hZ _ (S₀.le_shiftClosure _ ⟨d, hd, rfl⟩)
  exact (criterionPerfHomComparison_op_iff F X Y).1 (hsource X hX (op Y) hY)

end SerrePositivity.DifferentialGraded.Morita
