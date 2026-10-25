module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleNativeReadout

/-!
概要：Ind-S (9) の二つの実全族空間と、その元の族への厳密回収。
方針：要求正本の vertexFiber を名前付きで定義し、関手頂点の逆で値を読む。
規約：元の全 K と元のホーンを固定する。近似模型への置換はしない。
使われ方：全族空間間の longHom と encode の公開型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の内ホーンを全入力で厳密に固定した実二胞体族の空間。 -/
abbrev controlledTriangleFamilySpace (K : SSet.{u + 1})
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u}) : SSet.{u + 1} :=
  vertexFiber ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app SpaceInfinity.{u}) (functorVertex a)

/-- 元の合成端を全入力で厳密に固定した実全長 Hom 族の空間。 -/
abbrev controlledTriangleLongHomSpace (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) : SSet.{u + 1} :=
  vertexFiber ((ihom K).map (evaluateFunctorAt
    (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))
    (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (ULift.up (ComposableArrows.mk₀ triangleFullPath)))) (functorVertex c)

lemma controlledTriangleFamilySpace_isContractibleKan (K : SSet.{u + 1})
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u}) :
    IsContractibleKan (controlledTriangleFamilySpace K a) :=
  innerHornFamilyExtensionSpace_isContractibleKan 2 1 (by decide) (by decide) K a

lemma controlledTriangleLongHomSpace_isContractibleKan (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) :
    IsContractibleKan (controlledTriangleLongHomSpace X Z K c) :=
  triangleLongHomFamilyFiber_isContractibleKan.{u, u + 1} _ _ c

/-- 全族空間の一点が表す元の二胞体族。 -/
def controlledTriangleFamilyValue {K : SSet.{u + 1}}
    {a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u}}
    (t : (controlledTriangleFamilySpace K a) _⦋0⦌) :
    (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u} :=
  (functorVertexEquiv _ _).symm t.val

/-- 読み出した二胞体族は元の全ホーンを厳密に回収する。 -/
lemma controlledTriangleFamilyValue_horn {K : SSet.{u + 1}}
    {a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u}}
    (t : (controlledTriangleFamilySpace K a) _⦋0⦌) :
    ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ controlledTriangleFamilyValue t = a := by
  apply functorVertex_injective
  have ht : ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app SpaceInfinity).app
      (Opposite.op ⦋0⦌) t.val = functorVertex a :=
    t.property.trans (pinchedConstant_zero _)
  change ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app SpaceInfinity).app _
    (functorVertex (controlledTriangleFamilyValue t)) = _
  rw [show functorVertex (controlledTriangleFamilyValue t) = t.val from
    (functorVertexEquiv _ _).apply_symm_apply t.val]
  exact ht

/-- 合成端固定の長 Hom 全族を、その実全族空間の一点として登録する。 -/
def controlledTriangleLongHomVertex (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)))
    (hq : q ≫ evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))
      (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
      (ULift.up (ComposableArrows.mk₀ triangleFullPath)) = c) :
    (controlledTriangleLongHomSpace X Z K c) _⦋0⦌ :=
  ⟨functorVertex q, by
    rw [pinchedConstant_zero]
    change functorVertex (q ≫ evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))
      (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
      (ULift.up (ComposableArrows.mk₀ triangleFullPath))) = functorVertex c
    rw [hq]⟩

lemma controlledTriangleLongHomVertex_value (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))) (hq) :
    (functorVertexEquiv _ _).symm (controlledTriangleLongHomVertex X Z K c q hq).val = q :=
  (functorVertexEquiv _ _).symm_apply_apply q

end SerrePositivity.InfinityCategories
