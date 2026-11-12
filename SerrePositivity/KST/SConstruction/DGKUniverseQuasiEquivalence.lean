module
public import SerrePositivity.KST.SConstruction.DGKUniverseInput
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 固定入力の対象宇宙の上げ下げの準同値
概要：対象ラベルだけの上げ下げは元の全 Hom を同型で保ち、H⁰ で本質的全射。
方針：全 Hom 恒等射と元の指定対象の明示的な上げ下げを使う。
規約：元の dg 関手を選び直さない。使われ方：S 内の Morita 射の宇宙変更。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

/-- 同じ対象ラベルを下げる元の射は、全 Hom 恒等射を持つ実準同値。 -/
lemma dgKUniverseLiftDown_quasiEquivalence :
    QuasiEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, w} R D) := by
  refine ⟨?_, ⟨?_⟩⟩
  · intro x y
    change QuasiIso (𝟙 _)
    constructor
    intro n
    exact quasiIsoAt_of_isIso (𝟙 _) n
  · rintro ⟨y⟩
    refine ⟨(toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, w} D)).obj
      (ForgetEnrichment.of (Complex R)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, w} R D).obj (ForgetEnrichment.to (Complex R) y))), ?_⟩
    exact ⟨Iso.refl _⟩

/-- 同じ対象を持ち上げる元の射も、全 Hom 恒等射を持つ実準同値。 -/
lemma dgKUniverseLiftUp_quasiEquivalence :
    QuasiEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, w} R D) := by
  refine ⟨?_, ⟨?_⟩⟩
  · intro x y
    change QuasiIso (𝟙 _)
    constructor
    intro n
    exact quasiIsoAt_of_isIso (𝟙 _) n
  · rintro ⟨y⟩
    refine ⟨(toHomotopy R D).obj (ForgetEnrichment.of (Complex R)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, w} R D).obj (ForgetEnrichment.to (Complex R) y))), ?_⟩
    obtain ⟨y⟩ := y
    obtain ⟨y⟩ := y
    exact ⟨Iso.refl _⟩

end SerrePositivity.KST.SConstruction
