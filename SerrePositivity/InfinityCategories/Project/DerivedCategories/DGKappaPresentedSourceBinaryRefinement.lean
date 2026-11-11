module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedCommonSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceCommonOperations
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
/-!
概要：異なる出発コードと arrow を持つ二つの提示対象の直和を同じ提示模型で表す。
方針：二つの出発圏を一つへまとめ、seed の精密化と共通源の二項直和を使う。
規約：実値をホモトピー同型で比較し、任意標的閉射の持ち上げを仮定しない。
使われ方：c′ ゲート3の二項直和の同時精密化。
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
lemma dgKappaPresentedSource_binary_homotopyCovers
    (A B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    ∃ Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ,
      Nonempty ((moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y)) ≅
        (moduleToHomotopy R D).obj
          ((ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ A)) ⨿
            (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ B)))) := by
  let Z : ULift.{u} Bool → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ :=
    fun n => if n.down then B else A
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSourceCodeCoproductShape_nonempty R κ (fun n => (Z n).code) hreg
    (lt_trans (show Cardinal.mk (ULift.{u} Bool) < Cardinal.aleph0 by simp) hκ)
  let c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedCommonCode R D κ Z s
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedCommonArrow R D κ Z s
  obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedCommonSource_seedCovers R D κ hκ hreg Z s (ULift.up false)
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedCommonSource_seedCovers R D κ hκ hreg Z s (ULift.up true)
  let K := moduleToHomotopy R D
  let M := (dgModuleExtension R (c.Objects R κ) D L).onClosed.obj
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i)
  let N := (dgModuleExtension R (c.Objects R κ) D L).onClosed.obj
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceCommonBinary R D κ hκ hreg c L i j, ⟨?_⟩⟩
  exact K.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceCommonBinaryIso R D κ hκ hreg c L i j) ≪≫
    (PreservesColimitPair.iso K M N).symm ≪≫ coprod.mapIso hi.some hj.some ≪≫
    PreservesColimitPair.iso K _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
