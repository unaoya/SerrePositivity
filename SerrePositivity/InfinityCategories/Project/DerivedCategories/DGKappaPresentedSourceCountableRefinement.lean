module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedCommonSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceCommonOperations
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
/-!
概要：異なる出発コードと arrow を持つ可算個の提示対象の直和を同じ提示模型で表す。
方針：出発圏を一つへまとめ、各 seed を精密化して共通源の可算直和を評価する。
規約：実値の比較はホモトピー同型とする。任意標的閉射の cone 被覆は別課題。
使われ方：c′ ゲート3の可算直和の同時精密化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory CategoryTheory.Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D]
  (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)

include hκ hreg in
lemma dgKappaPresentedSource_countable_homotopyCovers
    (X : ℕ → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    ∃ Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ,
      Nonempty ((moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y)) ≅
        (moduleToHomotopy R D).obj (∐ (fun n : ℕ => ForgetEnrichment.of (Complex R)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ (X n))))) := by
  let Z : ULift.{u} ℕ → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ := fun n => X n.down
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSourceCodeCoproductShape_nonempty R κ (fun n => (Z n).code) hreg
    (show Cardinal.mk (ULift.{u} ℕ) < κ by simpa using hκ)
  let c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedCommonCode R D κ Z s
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedCommonArrow R D κ Z s
  have h : ∀ n : ℕ, ∃ i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1,
      Nonempty ((moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ ⟨c, i, L⟩)) ≅
        (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ (X n)))) :=
    fun n => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedCommonSource_seedCovers R D κ hκ hreg Z s (ULift.up n)
  choose i hi using h
  let K := moduleToHomotopy R D
  let M : ℕ → ModuleCategory R D := fun n =>
    (dgModuleExtension R (c.Objects R κ) D L).onClosed.obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c (i n))
  let N : ℕ → ModuleCategory R D := fun n =>
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ (X n))
  have e (n : ℕ) : K.obj (M n) ≅ K.obj (N n) := (hi n).some
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceCommonCountable R D κ hκ hreg c L i, ⟨?_⟩⟩
  exact K.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceCommonCountableIso R D κ hκ hreg c L i) ≪≫
    PreservesCoproduct.iso K M ≪≫ Sigma.mapIso e ≪≫ (PreservesCoproduct.iso K N).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
