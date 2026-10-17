module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Universal
public import Mathlib.Data.ZMod.Basic

/-! # 自由dg圏の結合則・K-flat Hom・厳密普遍性の監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.FreeDGCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]
  (E : Type w) [DGCategory A E]

example (K : ComplexQuiver A D) : DGCategory A (Objects A D K) := inferInstance

example (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y)) :
    localHomKFlat A (Objects A D K) := homKFlat A D K hK

example (K : ComplexQuiver A D) :
    DGFunctor A (Objects A D K) E ≃ GeneratorMap A D E K := universalEquiv A D E K

-- 対象写像と生成辺のchain mapだけからdg関手が一意に定まる。
example (K : ComplexQuiver A D) (g : GeneratorMap A D E K) :
    ∃! F : DGFunctor A (Objects A D K) E, restrict A D E K F = g := by
  refine ⟨extend A D E K g, restrict_extend A D E K g, ?_⟩
  intro F h
  exact extension_unique A D E K g F h

example (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E) :
    lift A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) = F :=
  lift_reconstruction A D E K F

example (D : Type v) [Small.{0} D] (E : Type w) [DGCategory (ZMod 2) E]
    (K : ComplexQuiver (ZMod 2) D) :
    DGFunctor (ZMod 2) (Objects (ZMod 2) D K) E ≃ GeneratorMap (ZMod 2) D E K :=
  universalEquiv (ZMod 2) D E K

#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath_inclusion
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_left_inclusion
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendWord
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.edgePrefix
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.edgePrefix_unit
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.edgePrefix_nonempty
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath_unit
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendWord_cons
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath_edgePrefix
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_edgePrefix
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendWord_assoc
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath_assoc
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_assoc
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.Objects
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.objectsSmall
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.dgCategory
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homKFlat
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.lift
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.lift_edge
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_edge_path
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.functor_word
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.functor_path
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homEvaluation_reconstruction
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.lift_reconstruction
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.GeneratorMap
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.restrict
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.extend
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.extend_restrict
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.restrict_extend
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.universalEquiv
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.extension_unique
