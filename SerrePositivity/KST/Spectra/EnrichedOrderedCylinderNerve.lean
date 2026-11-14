module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedOrderedCylinder
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：元の coherent nerve と標準単体の積を、順序付き円柱の nerve へ組み合わせる。
方針：単体の順序写像で段を決め、thickening の path の順序から Hom の証明を作る。
規約：全単体で自然な実際の写像。使われ方：自然変換の因子分解の coherent な三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
variable {J : Type w} [Preorder J]
section
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- thickening の path は、単体の順序写像で選んだ段の順序の証明を与える。 -/
def pathOrderMap {n : ℕ} (t : Fin (n + 1) →o J)
    (X Y : SimplicialThickening (ULift.{u} (Fin (n + 1)))) :
    (X ⟶[SSet] Y) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.orderWitness J (t X.as.down) (t Y.as.down) where
  app _ := ↾fun P ↦ by
    have h : X.as ≤ Y.as := Path.le (P.obj 0)
    exact ⟨⟨t.monotone h⟩⟩
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro P
    exact Subsingleton.elim _ _

/-- 単体の順序写像と元の豊穣図式を組み合わせる。 -/
def simplexPair {n : ℕ} (t : Fin (n + 1) →o J)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening (ULift.{u} (Fin (n + 1)))) C) :
    EnrichedFunctor SSet.{u} (SimplicialThickening (ULift.{u} (Fin (n + 1)))) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) where
  obj X := ⟨t X.as.down, F.obj X⟩
  map X Y := lift (pathOrderMap t X Y) (F.map X Y)
  map_id X := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app (F.map_id X) d) PUnit.unit
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · let fg : ((X ⟶[SSet] Y) ⊗ (Y ⟶[SSet] Z)).obj d := (f, g)
      have h := ConcreteCategory.congr_hom (NatTrans.congr_app (F.map_comp X Y Z) d) fg
      exact h

/-- 元の豊穣圏から指定した段への包含。 -/
def stageInclusion (i : J) : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) where
  obj X := ⟨i, X⟩
  map X Y := {
    app _ := ↾fun f ↦ (⟨⟨le_rfl⟩⟩, f)
    naturality := by intros; rfl }
  map_id X := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    rfl
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    rfl

end
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の nerve と標準単体から、順序付き円柱の nerve への実際の pairing。 -/
def nerveSimplexFamily (m : ℕ) :
    SimplicialNerve C ⊗ (Δ[m] : SSet.{max u v}) ⟶
      SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin (m + 1)) C) where
  app _ := ↾fun ⟨F, t⟩ ↦ simplexPair (stdSimplex.asOrderHom t) F
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨F, t⟩
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    apply SSet.hom_ext
    intro d'
    apply ConcreteCategory.hom_ext
    intro P
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl

/-- 標準単体の指定頂点での制限は、元の豊穣圏のその段への包含。 -/
lemma nerveSimplexFamily_vertex (m : ℕ) (i : Fin (m + 1)) :
    lift (𝟙 (SimplicialNerve C)) (SSet.const (stdSimplex.obj₀Equiv.symm i)) ≫
        nerveSimplexFamily m = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stageInclusion (C := C) i) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  apply SSet.hom_ext
  intro e
  apply ConcreteCategory.hom_ext
  intro P
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

end SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
