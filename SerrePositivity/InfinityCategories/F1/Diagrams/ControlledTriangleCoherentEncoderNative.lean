module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleUniversalNative

/-!
概要：実 coherent encoder は、元の各長 Hom 全族を各 k の full native Hom として回収する。
方針：実二胞体族を同じ k・l へ制限し、全 native 区間の回収式を適用する。
規約：直接 path の値だけではなく、native Hom 関手全体の HEq。
使われ方：Ind-S (9) の単射 encoder に必要な回収条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

private lemma triangleNative_heq_of_normalized
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {T : SSet.{u}}
    {A B X Z : C} (hA : A = X) (hB : B = Z)
    (m : T ⟶ SimplicialCategory.sHom A B) (n : T ⟶ SimplicialCategory.sHom X Z)
    (h : m ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) = n) : HEq m n := by
  subst X Z
  simp only [eqToHom_refl, Category.comp_id] at h
  exact heq_of_eq h

variable (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
  (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))

lemma controlledTriangleCoherentFamily_at_pair
    (l : (controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)) _⦋0⦌)
    (k : K _⦋0⦌) :
    SSet.yonedaEquiv (familyAtVertex (controlledTriangleCoherentFamily X Y Z K f g) (k, l)) =
      triangleSeparatedSimplex f g (controlledTriangleSeparatedExtension X Y Z K f g)
        (controlledTriangleSeparatedExtension_comp X Y Z K f g)
        (PinchedHom.constant k 2) (PinchedHom.constant l 2)
        (OrderHom.id : Fin 3 →o Fin 3) := by
  rfl

lemma controlledTriangleCoherentFamily_native
    (l : (controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)) _⦋0⦌)
    (k : K _⦋0⦌) :
    HEq ((controlledTriangleLongHomValue l).app (Opposite.op ⦋0⦌) k)
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (familyAtVertex (controlledTriangleCoherentFamily X Y Z K f g)
          (k, l))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  rw [controlledTriangleCoherentFamily_at_pair]
  let M := controlledTriangleSeparatedExtension X Y Z K f g
  let s := PinchedHom.constant k 2
  let r := PinchedHom.constant l 2
  let t : Fin 3 →o Fin 3 := OrderHom.id
  let F := triangleSeparatedSimplex f g M (controlledTriangleSeparatedExtension_comp X Y Z K f g) s r t
  have hX : F.obj ⟨ULift.up 0⟩ = X := triangleSeparatedBaseline_obj_zero f g s t 0 rfl
  have hZ : F.obj ⟨ULift.up 2⟩ = Z := triangleSeparatedBaseline_obj_two f g s t 2 rfl
  have hn : F.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom hX hZ) =
        triangleSeparatedLongHom M s r t (i := 0) rfl 2 :=
    triangleSeparatedAssignedHom_long f g M s r t 0 2 rfl rfl
  have hh := triangleNative_heq_of_normalized hX hZ _ _ hn
  have hu := uliftHomFunctorVertex_heq.{u, u + 1}
    (congrArg₂ SimplicialCategory.sHom hX hZ) _ _ hh
  exact ((hu.trans (heq_of_eq
    (controlledTriangleSeparatedExtension_native_value X Y Z K f g l k)))).symm

variable (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u})
  (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
    (Δ[1] ◁ f) ≫ intervalMappingUncurry (coherentHomIntervalComparison X Y))
  (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
    (Δ[1] ◁ g) ≫ intervalMappingUncurry (coherentHomIntervalComparison Y Z))

/-- 同じ実 encoder と元の固定ホーンでの、各入力の全 native Hom の回収。 -/
lemma controlledTriangleCoherentEncoder_native
    (l : (controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)) _⦋0⦌)
    (k : K _⦋0⦌) :
    HEq ((controlledTriangleLongHomValue l).app (Opposite.op ⦋0⦌) k)
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (familyAtVertex (controlledTriangleFamilyValue
          ((controlledTriangleCoherentEncoder X Y Z K f g a hf hg).app (Opposite.op ⦋0⦌) l))
          k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  rw [controlledTriangleCoherentEncoder_value]
  have he : familyAtVertex
      ((Δ[2] ◁ lift (𝟙 K) (SSet.const l)) ≫ controlledTriangleCoherentFamily X Y Z K f g) k =
        familyAtVertex (controlledTriangleCoherentFamily X Y Z K f g) (k, l) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    rfl
  rw [he]
  exact controlledTriangleCoherentFamily_native X Y Z K f g l k

end SerrePositivity.InfinityCategories
