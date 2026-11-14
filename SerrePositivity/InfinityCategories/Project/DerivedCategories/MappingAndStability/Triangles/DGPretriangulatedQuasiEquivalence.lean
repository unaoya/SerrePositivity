module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedTria
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction

/-! # dg 準同値に沿う前三角性の反映

概要：dg 準同値の標的が前三角なら始域も前三角。
方針：導来拡張で有限 cell を送り、代表対象の本質的全射性と完全忠実性で同型を戻す。
規約：K(D) の同型への帰還は有限 cell 比較を通す。使われ方：平坦 cell 分解の前三角性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 実導来拡張は任意 dg 関手に沿って有限 cell の本質像を保つ。 -/
lemma dgDerivedExtension_finiteCell {X : DerivedModuleCategory A D}
    (hX : derivedFiniteCellOver A D Set.univ X) :
    derivedFiniteCellOver A E Set.univ ((dgDerivedExtension A D E F).obj X) :=
  graphDerivedExtension_derivedFiniteCell_mem A D E F
    (derivedFiniteCellOver A E Set.univ) Set.univ
    (fun x _ => (moduleFiniteCellOver A E Set.univ).prop_map_obj (moduleToDerived A E)
      (moduleFiniteCell_representable A E (F.obj x))) hX

/-- 準同値の標的の前三角性を始域へ戻す。 -/
lemma isDGPretriangulated_of_quasiEquivalence [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A E]
    (hF : QuasiEquivalence F) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_tria_representable A D
  intro X
  let H := dgDerivedExtension A D E F
  let Y : TriaCategory A E := ⟨H.obj X.obj, dgDerivedExtension_finiteCell A D E F X.property⟩
  obtain ⟨e, ⟨he⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTria_isRepresentable A E Y
  obtain ⟨d, ⟨hd⟩⟩ := dgDerivedExtension_representable_essImage A D E F hF.2 e
  let hi : H.obj X.obj ≅ H.obj (triaRepresentable A D d).obj :=
    (triaInclusion A E).mapIso he ≪≫ hd.symm
  exact ⟨d, ⟨(derivedFiniteCellOver A D Set.univ).isoMk
    ((dgDerivedExtensionFullyFaithful A D E F hF.1).preimageIso hi)⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
