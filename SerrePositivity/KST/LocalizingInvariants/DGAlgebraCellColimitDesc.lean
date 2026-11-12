module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellStages

/-!
概要：互換な段階代数射を実 cell 分解からの代数射へ貼り合わせる。
方針：Hom 列の余極限で射を作り、単位と積は段階包含で検査する。
規約：代数圏での余極限保存を入力しない。使われ方：全射準同型を通る持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGCategoryCellResolution
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  (f : ∀ n, cellStage R B n ⟶ C)
  (hf : ∀ n, cellStageTransition R B n ≫ f (n + 1) = f n)

def cellStageMapCocone : Cocone (homDiagram R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) .star .star) where
  pt := C.X
  ι := NatTrans.ofSequence (fun n => (f n).hom) (fun n => by
    change (homDiagram R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) .star .star).map
      (homOfLE (Nat.le_succ n)) ≫ (f (n + 1)).hom = (f n).hom ≫ 𝟙 _
    dsimp only [homDiagram]
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    exact congrArg Mon.Hom.hom (hf n))

def cellColimitDescHom : (cellResolution R B).X ⟶ C.X :=
  colimit.desc _ (cellStageMapCocone R f hf)

@[reassoc]
lemma cellColimitDescHom_stage (n : ℕ) :
    (cellStageInclusion R B n).hom ≫ cellColimitDescHom R f hf = (f n).hom :=
  colimit.ι_desc _ _

lemma cellColimitDescHom_one :
    η[(cellResolution R B).X] ≫ cellColimitDescHom R f hf = η[C.X] := by
  change candidateUnit R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) .star ≫ cellColimitDescHom R f hf = _
  rw [candidateUnit, Category.assoc]
  change η[(cellStage R B 0).X] ≫
    ((cellStageInclusion R B 0).hom ≫ cellColimitDescHom R f hf) = _
  rw [cellColimitDescHom_stage, IsMonHom.one_hom]

lemma cellColimitDescHom_mul :
    μ[(cellResolution R B).X] ≫ cellColimitDescHom R f hf =
      (cellColimitDescHom R f hf ⊗ₘ cellColimitDescHom R f hf) ≫ μ[C.X] := by
  apply (candidateTensorIsColimit R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) .star .star .star).hom_ext
  intro n
  change (stageInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n .star .star ⊗ₘ
    stageInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) n .star .star) ≫
      (candidateComposition R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) .star .star .star ≫
        cellColimitDescHom R f hf) = _
  rw [← Category.assoc, candidateComposition_stage, Category.assoc]
  change μ[(cellStage R B n).X] ≫
    ((cellStageInclusion R B n).hom ≫ cellColimitDescHom R f hf) =
      ((cellStageInclusion R B n).hom ⊗ₘ (cellStageInclusion R B n).hom) ≫
        (cellColimitDescHom R f hf ⊗ₘ cellColimitDescHom R f hf) ≫ μ[C.X]
  rw [cellColimitDescHom_stage, ← Category.assoc, tensorHom_comp_tensorHom,
    cellColimitDescHom_stage]
  exact IsMonHom.mul_hom (f n).hom

def cellColimitDesc : cellResolution R B ⟶ C :=
  Mon.Hom.mk' (cellColimitDescHom R f hf)
    (cellColimitDescHom_one R f hf) (cellColimitDescHom_mul R f hf)

lemma cellColimitDesc_stage (n : ℕ) :
    cellStageInclusion R B n ≫ cellColimitDesc R f hf = f n := by
  apply Mon.Hom.ext
  exact cellColimitDescHom_stage R f hf n

lemma cellColimitDesc_projection (p : C ⟶ B)
    (hp : ∀ n, f n ≫ p = cellStageAugmentation R B n) :
    cellColimitDesc R f hf ≫ p = cellAugmentation R B := by
  apply Mon.Hom.ext
  apply colimit.hom_ext
  intro n
  change (cellStageInclusion R B n).hom ≫ (cellColimitDescHom R f hf ≫ p.hom) =
    (cellStageInclusion R B n).hom ≫ (cellAugmentation R B).hom
  rw [← Category.assoc, cellColimitDescHom_stage]
  exact (congrArg Mon.Hom.hom (hp n)).trans
    (congrArg Mon.Hom.hom (cellStageInclusion_augmentation R B n)).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
