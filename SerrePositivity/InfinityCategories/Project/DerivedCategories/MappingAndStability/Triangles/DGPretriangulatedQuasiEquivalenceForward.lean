module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedQuasiEquivalence
/-!
概要：dg 準同値の始域の前三角性を標的へ移送する。
方針：実導来逆関手が有限 cell を保つことを代表から証明し、同じ余単位で代表へ戻す。
規約：全 Perf の Small 性を仮定せず、元の dg 準同値を保持する。
使われ方：D-18 補足。小 Perf 模型から既存の小 dg 包絡模型への前三角性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedRestriction_finiteCell_of_quasiEquivalence (hF : QuasiEquivalence F)
    {X : DerivedModuleCategory A E} (hX : derivedFiniteCellOver A E Set.univ X) :
    derivedFiniteCellOver A D Set.univ ((dgDerivedRestriction A D E F).obj X) := by
  let H := dgDerivedRestriction A D E F
  letI : H.CommShift ℤ := dgDerivedRestrictionCommShift A D E F
  letI : H.IsTriangulated := dgDerivedRestrictionIsTriangulated A D E F
  let P := (derivedFiniteCellOver A D Set.univ).inverseImage H
  haveI : P.IsTriangulated := by dsimp [P]; infer_instance
  haveI : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  apply ((derivedFiniteCellOver_le_iff_generators A E P Set.univ).2 ?_) X hX
  intro e _
  obtain ⟨d, ⟨ed⟩⟩ := dgDerivedExtension_representable_essImage A D E F hF.2 e
  exact (derivedFiniteCellOver A D Set.univ).prop_of_iso
    ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app _ ≪≫ H.mapIso ed)
    (triaRepresentable A D d).property

lemma isDGPretriangulated_of_quasiEquivalence_forward [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (hF : QuasiEquivalence F) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A E := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_tria_representable A E
  intro X
  let H := dgDerivedExtension A D E F
  let K := dgDerivedRestriction A D E F
  let Y : TriaCategory A D :=
    ⟨K.obj X.obj, dgDerivedRestriction_finiteCell_of_quasiEquivalence A D E F hF X.property⟩
  obtain ⟨d, ⟨ed⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTria_isRepresentable A D Y
  exact ⟨F.obj d, ⟨(derivedFiniteCellOver A E Set.univ).isoMk
    (((dgFunctorDerivedEquivalence A D E F hF).counitIso.app X.obj).symm ≪≫
      H.mapIso ((triaInclusion A D).mapIso ed) ≪≫
        dgDerivedExtensionRepresentableIso A D E F d)⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
