module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulated
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：実表現可能加群の演算から前三角性を判定する。
方針：零・shift・cone の表現可能性から全三角形への閉性を得る。
規約：Yoneda の全 Hom と実三角同型を使う。
使われ方：加群の選択代表部分圏の一般判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
section
open CategoryTheory DifferentialGraded Pretriangulated
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma isDGPretriangulated_of_representable_operations
    (hzero : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R C).ContainsZero)
    (hshift : ∀ (X : C) (n : ℤ),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable R C (shiftModule n (representable R X)))
    (hcone : ∀ (X Y : C)
      (f : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable R C (ForgetEnrichment.to (Complex R)
        (moduleCone R C ((dgYoneda R C).onClosed.map f)))) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C := by
  let P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R C
  let K := moduleToHomotopy R C
  have hs : P.IsStableUnderShift ℤ := by
    refine ⟨fun n ↦ ⟨fun A hA ↦ ?_⟩⟩
    obtain ⟨X, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R C A).1 hA
    have hX : P ((K.obj (ForgetEnrichment.of (Complex R) (representable R X)))⟦n⟧) :=
      P.prop_of_iso ((K.commShiftIso n).app
        (ForgetEnrichment.of (Complex R) (representable R X))) (hshift X n)
    exact P.prop_of_iso ((shiftFunctor _ n).mapIso e).symm hX
  have ht : P.IsTriangulatedClosed₃ := by
    refine ⟨fun T hT h₁ h₂ ↦ ?_⟩
    obtain ⟨X, ⟨eX⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R C _).1 h₁
    obtain ⟨Y, ⟨eY⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R C _).1 h₂
    have hfull : (dgYoneda R C).onClosed.Full :=
      (dgYoneda R C).onClosed_full_of_homIso (fun x y ↦ by
        change IsIso (dgYonedaIso R x (representable R y)).inv
        infer_instance)
    let := hfull
    let fk := eX.inv ≫ T.mor₁ ≫ eY.hom
    obtain ⟨g, hg⟩ := K.map_surjective fk
    obtain ⟨g, rfl⟩ := (dgYoneda R C).onClosed.map_surjective g
    let U := moduleHomotopyConeTriangle R C ((dgYoneda R C).onClosed.map g)
    have hU : U ∈ distTriang (ModuleHomotopyCategory R C) :=
      moduleHomotopyConeTriangle_distinguished R C ((dgYoneda R C).onClosed.map g)
    have hc : P U.obj₃ := hcone X Y g
    have hcomm : T.mor₁ ≫ eY.hom = eX.hom ≫ U.mor₁ := by
      change T.mor₁ ≫ eY.hom = eX.hom ≫ K.map ((dgYoneda R C).onClosed.map g)
      rw [hg]
      simp only [fk, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    let e := isoTriangleOfIso₁₂ T U hT hU eX eY hcomm
    refine ⟨T.obj₃, P.prop_of_iso ((Triangle.π₃).mapIso e).symm hc, ⟨Iso.refl _⟩⟩
  let := hs
  let := ht
  exact {
    toContainsZero := hzero
    toIsStableUnderShift := hs
    toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃ }

end

end SerrePositivity.InfinityCategories.Project.DerivedCategories
