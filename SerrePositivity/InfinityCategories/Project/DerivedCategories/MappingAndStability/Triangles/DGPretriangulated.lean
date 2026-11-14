module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleHomotopyProperty
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # 表現可能加群の同型閉包による dg 前三角性

概要：全 dg 自然な K(D) における表現可能対象の同型閉包を使って前三角性を述べる。
方針：厳密な対象の等号による像に isoClosure を取り、三角的閉性を要求する。
規約：∞ 安定性を定義の入力にしない。使われ方：dg nerve の安定性と商の安定性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K(D) における表現可能加群の同型閉包。 -/
def dgRepresentableHomotopyProperty : ObjectProperty (ModuleHomotopyCategory A D) :=
  ObjectProperty.isoClosure (fun M => ∃ x : D, M = (moduleToHomotopy A D).obj
    (ForgetEnrichment.of (Complex A) (representable A x)))

/-- 表現可能対象の同型閉包は同型で閉じている。 -/
instance dgRepresentableHomotopyProperty_isClosedUnderIsomorphisms :
    (dgRepresentableHomotopyProperty A D).IsClosedUnderIsomorphisms := by
  unfold dgRepresentableHomotopyProperty
  infer_instance

/-- 閉包に属することはある表現可能加群との K(D) の同型を持つこと。 -/
lemma dgRepresentableHomotopyProperty_iff (M : ModuleHomotopyCategory A D) :
    dgRepresentableHomotopyProperty A D M ↔
      ∃ x : D, Nonempty (M ≅ (moduleToHomotopy A D).obj
        (ForgetEnrichment.of (Complex A) (representable A x))) := by
  constructor
  · rintro ⟨N, ⟨x, rfl⟩, e⟩
    exact ⟨x, e⟩
  · rintro ⟨x, e⟩
    exact ⟨_, ⟨x, rfl⟩, e⟩

/-- 各表現可能加群はその同型閉包に属する。 -/
lemma dgRepresentableHomotopyProperty_representable (x : D) :
    dgRepresentableHomotopyProperty A D ((moduleToHomotopy A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) :=
  (dgRepresentableHomotopyProperty_iff A D _).2 ⟨x, ⟨Iso.refl _⟩⟩

/-- dg 前三角性：表現可能対象の同型閉包が零・整数シフト・三角形で閉じる。 -/
abbrev IsDGPretriangulated : Prop :=
  (dgRepresentableHomotopyProperty A D).IsTriangulated

/-- 全 dg 加群におけるホモトピー表現可能性。 -/
def dgHomotopyRepresentable : RightModule A D → Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D (dgRepresentableHomotopyProperty A D)

/-- 元の対象の代表加群はホモトピー表現可能。 -/
lemma dgHomotopyRepresentable_representable (x : D) :
    dgHomotopyRepresentable A D (representable A x) :=
  dgRepresentableHomotopyProperty_representable A D x

end SerrePositivity.InfinityCategories.Project.DerivedCategories
