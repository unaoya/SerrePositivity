module

public import SerrePositivity.InfinityCategories.F2.Ind.FullSlicePullback
public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanShapeAmbient

/-!
概要：slice 引き戻しの同じ普遍余錐を、図式の表示変更と全部分包含で追跡する。
方針：元の全族の uncurry と、同じ引き戻しの第二射影を用いる。
規約：元の join からの射全体の厳密な等式。
使われ方：局所 Kan 余錐を元の密度余錐へ制限した際の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 右因子を固定する join の写像は、左因子の合成を厳密に保つ。 -/
lemma joinMap_comp_fixed {A B C K : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    joinMap (f ≫ g) (𝟙 K) = joinMap f (𝟙 K) ≫ joinMap g (𝟙 K) := by
  rw [← joinMap_comp, Category.id_comp]

/-- 同じ slice 引き戻しからの全普遍錐。 -/
def slicePullbackCoconeMap {A K X : SSet.{u}} (δ : A ⟶ X) (D : K ⟶ X) :
    join (pullback δ (sliceOverProjection D)) K ⟶ X :=
  sliceOverUncurry (pullback.snd δ (sliceOverProjection D))

/-- 固定図式の等式による移送は、普遍錐の元の全射を保つ。 -/
lemma slicePullbackCoconeMap_transport {A K X : SSet.{u}} (δ : A ⟶ X)
    {D D' : K ⟶ X} (h : D = D') :
    joinMap (eqToHom (congrArg (fun d => pullback δ (sliceOverProjection d)) h)) (𝟙 K) ≫
      slicePullbackCoconeMap δ D' = slicePullbackCoconeMap δ D := by
  subst D'
  rw [eqToHom_refl, joinMap_id, Category.id_comp]

/-- 始点図式の等式による移送も、普遍錐の元の全射を保つ。 -/
lemma slicePullbackCoconeMap_congrHom {A K X : SSet.{u}} {δ δ' : A ⟶ X}
    (h : δ = δ') (D : K ⟶ X) :
    joinMap (pullback.congrHom h rfl).hom (𝟙 K) ≫ slicePullbackCoconeMap δ' D =
      slicePullbackCoconeMap δ D := by
  subst δ'
  rw [slicePullbackCoconeMap, ← sliceOverUncurry_precomp]
  apply congrArg sliceOverUncurry
  simp only [pullback.congrHom, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]

/-- 全部分圏の同じ引き戻しの同型は、普遍錐を元の包含による後合成へ写す。 -/
lemma fullSlicePullbackIso_hom_coconeMap {A K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (δ : A ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (D : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})) :
    joinMap (fullSlicePullbackIso P δ D).hom (𝟙 K) ≫
      slicePullbackCoconeMap (δ ≫ (fullSubcomplexOnVertices X P).ι)
        (D ≫ (fullSubcomplexOnVertices X P).ι) =
      slicePullbackCoconeMap δ D ≫ (fullSubcomplexOnVertices X P).ι := by
  rw [slicePullbackCoconeMap, ← sliceOverUncurry_precomp]
  change sliceOverUncurry (fullSlicePullbackMap P δ D ≫ pullback.snd _ _) = _
  rw [fullSlicePullbackMap, pullback.lift_snd, sliceOverUncurry_postcomp]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
