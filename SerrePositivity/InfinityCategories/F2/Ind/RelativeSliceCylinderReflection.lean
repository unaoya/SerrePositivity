module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeJoinCylinderOverExtension
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeVertexIsoCylinder
public import SerrePositivity.InfinityCategories.Core.SliceMap
/-!
概要：評価後の全余錐を保つ実円柱の比較を、slice 内の相対同型へ戻す。
方針：標的への像を固定した join 円柱へ延長し、相対関手空間へ curry する。
規約：同型の全過程で評価後の全図式を厳密に保持する。
使われ方：指定始点評価の下での Ind 補間族の相対反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：同じ全評価を固定した余錐の実比較は、slice の相対関手空間内で同型。
方針：相対 join 円柱を curry する。規約：原の全射を保持。使われ方：comma への相対反映。 -/
lemma nonempty_sliceRelativeFunctorVertexIso_of_coconeCylinder
    {A K X Y : SSet.{u}} (p : K ⟶ X) (e : X ⟶ Y) (he : F1B.EquivalenceLifting e)
    (f g : A ⟶ sliceOver p) (a : A ⟶ sliceOver (p ≫ e))
    (hf : f ≫ sliceOverPostcomp p e = a) (hg : g ≫ sliceOverPostcomp p e = a)
    (V : join A K ⊗ equivalenceInterval ⟶ X)
    (h₀ : equivalenceCylinderEndpoint (join A K) false ≫ V = sliceOverUncurry f)
    (h₁ : equivalenceCylinderEndpoint (join A K) true ≫ V = sliceOverUncurry g)
    (hV : (joinInr A K ▷ equivalenceInterval) ≫ V = fst K equivalenceInterval ≫ p)
    (hVe : V ≫ e = fst (join A K) equivalenceInterval ≫ sliceOverUncurry f ≫ e) :
    Nonempty (VertexIso
      (relativeFunctorVertex (sliceOverPostcomp p e) a f hf)
      (relativeFunctorVertex (sliceOverPostcomp p e) a g hg)) := by
  obtain ⟨F, hF₀, hF₁, hFe⟩ := exists_joinCylinder_extension_of_equivalenceFamily_over
    e he (sliceOverUncurry f) (sliceOverUncurry g)
    (by rw [sliceOverUncurry_fixed, sliceOverUncurry_fixed]) V h₀ h₁
    (by rw [sliceOverUncurry_fixed]; exact hV) hVe
  have hFp : joinInr (A ⊗ equivalenceInterval) K ≫ F = p := by
    have h := congrArg (fun z => joinInr A K ≫ z) hF₀
    simpa only [← Category.assoc, joinInr_joinMap, Category.id_comp,
      sliceOverUncurry_fixed] using h
  let G := sliceOverCurry F hFp
  have G₀ : equivalenceCylinderEndpoint A false ≫ G = f := by
    apply sliceOverUncurry_injective
    rw [sliceOverUncurry_precomp]
    dsimp only [G]
    rw [sliceOverUncurry_curry]
    exact hF₀
  have G₁ : equivalenceCylinderEndpoint A true ≫ G = g := by
    apply sliceOverUncurry_injective
    rw [sliceOverUncurry_precomp]
    dsimp only [G]
    rw [sliceOverUncurry_curry]
    exact hF₁
  have Ga : G ≫ sliceOverPostcomp p e = fst A equivalenceInterval ≫ a := by
    apply sliceOverUncurry_injective
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_precomp]
    dsimp only [G]
    rw [sliceOverUncurry_curry, hFe]
    have ha := congrArg sliceOverUncurry hf
    rw [sliceOverUncurry_postcomp] at ha
    rw [ha]
  exact nonempty_relativeFunctorVertexIso_of_equivalenceCylinder
    (sliceOverPostcomp p e) a f g hf hg G G₀ G₁ Ga
end SerrePositivity.InfinityCategories.F2.Ind
