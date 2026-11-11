module
public import SerrePositivity.KST.SConstruction.SimplexHAInverseFunctor
public import SerrePositivity.KST.SConstruction.CubicalLambdaPointPair

/-!
概要：元 native 一単体の Λ 逆 Hom 作用を、同じ増大と元閉辺で回収する。
方針：零次元の厳密区間復元と同じ余モノイド比較の増大則を使う。
規約：元辺の全複体作用を保持し、頂点別一致へ弱めない。
使われ方：全 end 辺の native 評価と元厳密変換のホモトピーの比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open scoped Simplicial ComonObj

/-- 概要：元一単体の厳密区間 Hom 作用は同じ増大後の元閉辺。
方針：元零次元 cube の実復元と余モノイド比較を照合する。
規約：全複体射の等号。使われ方：元 end 辺の全 Hom 評価。 -/
lemma simplexHAEdgeHomMap_augmentation (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1) :
    simplexHAHomMap R s 0 1 =
      ε[(cubicalLambdaHomComonoid R (Δ[1] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 1)).X] ≫
          unitFromCycle _ (s.edgeCycle 0 1 (by decide)) := by
  rw [simplexHAHomMap_of_lt R s 0 1 (by decide)]
  unfold simplexHAIntervalHomMap simplexHAIntervalChainLift
  have hz := simplexHAChainLift_zero R s
    (simplexHAStrictIntervalOrder (0 : Fin 2) 1 (by decide)) 1
    (simplexHAStrictIntervalOrder_last_lt (0 : Fin 2) 1 (by decide))
  have hh := congrArg (fun f =>
    (simplexIntervalLambdaHomIso R (0 : Fin 2) 1 (by decide)).inv ≫ f) hz
  apply hh.trans
  change (simplexIntervalLambdaHomIso R (0 : Fin 2) 1 (by decide)).inv ≫
      unitFromCycle _ (s.edgeCycle 0 1 (by decide)) = _
  have he : (simplexIntervalLambdaHomIso R (0 : Fin 2) 1 (by decide)).hom ≫
      ε[(cubicalLambdaHomComonoid R (Δ[1] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 1)).X] =
      𝟙 (𝟙_ (Complex R)) :=
    simplexIntervalLambdaHomIso_augmentation R (0 : Fin 2) 1 (by decide)
  have hi : (simplexIntervalLambdaHomIso R (0 : Fin 2) 1 (by decide)).inv =
      ε[(cubicalLambdaHomComonoid R (Δ[1] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 1)).X] :=
    (cancel_epi (simplexIntervalLambdaHomIso R (0 : Fin 2) 1 (by decide)).hom).mp
      ((simplexIntervalLambdaHomIso R (0 : Fin 2) 1 (by decide)).hom_inv_id.trans he.symm)
  exact congrArg (fun f => f ≫ unitFromCycle _ (s.edgeCycle 0 1 (by decide))) hi

/-- 概要：元 native 一単体の実逆 dg 関手も同じ増大と元閉辺を回収する。
方針：元頂点間の Hom 回収則へ同じ全複体等号を合成する。
規約：元一単体を変更しない。使われ方：元全 end 辺の評価比較。 -/
lemma simplexHAEdgeInverseFunctor_augmentation (R : Type u) [CommRing R]
    (E : Type v) [DGCategory R E] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1) :
    (simplexHAInverseFunctor R s).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 1) =
      ε[(cubicalLambdaHomComonoid R (Δ[1] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 1)).X] ≫
          unitFromCycle _ (s.edgeCycle 0 1 (by decide)) :=
  (simplexHAInverseFunctor_map_vertices R s 0 1).trans
    (simplexHAEdgeHomMap_augmentation R E s)


/-- 概要：元 native 一単体の全二頂点間に、同じ単位・閉辺・逆向き零の係数を保持する。
方針：元二頂点の四場合を使う。規約：元閉辺を変更しない。
使われ方：退化を含む元区間全 Hom 作用の増大表示。 -/
def simplexHAEdgeCoefficient (R : Type u) [CommRing R]
    (E : Type v) [DGCategory R E] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1) (a b : Fin 2) :
    𝟙_ (Complex R) ⟶ homObject R E (s.obj a) (s.obj b) := by
  refine Fin.cases ?_ (fun a₀ => ?_) a
  · refine Fin.cases ?_ (fun b₀ => ?_) b
    · exact eId (Complex R) (s.obj 0)
    · obtain rfl : b₀ = 0 := Subsingleton.elim _ _
      exact unitFromCycle _ (s.edgeCycle 0 1 (by decide))
  · obtain rfl : a₀ = 0 := Subsingleton.elim _ _
    refine Fin.cases ?_ (fun b₀ => ?_) b
    · exact 0
    · obtain rfl : b₀ = 0 := Subsingleton.elim _ _
      exact eId (Complex R) (s.obj 1)

/-- 概要：元 native 区間の実逆関手の全 Hom 作用は元増大と同じ区間係数。
方針：対角の増大・単位、元閉辺、逆向き零を四場合で照合する。
規約：全複体射の等号。使われ方：元全 end 辺の native 評価。 -/
lemma simplexHAEdgeInverseFunctor_allHom_augmentation (R : Type u) [CommRing R]
    (E : Type v) [DGCategory R E] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1) (a b : Fin 2) :
    (simplexHAInverseFunctor R s).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      ε[(cubicalLambdaHomComonoid R (Δ[1] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)).X] ≫
          simplexHAEdgeCoefficient R E s a b := by
  apply (simplexHAInverseFunctor_map_vertices R s a b).trans
  fin_cases a <;> fin_cases b
  · exact simplexHAHomMap_self R s 0
  · exact simplexHAEdgeHomMap_augmentation R E s
  · exact (simplexHAHomMap_of_gt R s 1 0 (by decide)).trans (Limits.comp_zero).symm
  · exact simplexHAHomMap_self R s 1


/-- 概要：元 native 区間の全 Λ 対象で同じ区間係数を保持する。
方針：元頂点番号の逆対応を使う。規約：元全対象を保持。
使われ方：任意パラメータ上への元区間 Hom 作用の引き戻し。 -/
def simplexHAEdgeObjectCoefficient (R : Type u) [CommRing R]
    (E : Type v) [DGCategory R E] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1)
    (x y : CubicalLambda R (Δ[1] : SSet.{u})) :
    𝟙_ (Complex R) ⟶ homObject R E
      ((simplexHAInverseFunctor R s).obj x) ((simplexHAInverseFunctor R s).obj y) :=
  simplexHAEdgeCoefficient R E s ((simplexLambdaVertexEquiv R 1).symm x)
    ((simplexLambdaVertexEquiv R 1).symm y)

/-- 概要：元区間の全 Λ 対象間の Hom 作用は同じ増大と元係数。
方針：元頂点対応の全射性で同じ全 Hom 等号を回収する。
規約：全複体射を保持。使われ方：全パラメータ変換の増大則。 -/
lemma simplexHAEdgeInverseFunctor_objects_augmentation (R : Type u) [CommRing R]
    (E : Type v) [DGCategory R E] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1)
    (x y : CubicalLambda R (Δ[1] : SSet.{u})) :
    (simplexHAInverseFunctor R s).map x y =
      ε[(cubicalLambdaHomComonoid R (Δ[1] : SSet.{u}) x y).X] ≫
        simplexHAEdgeObjectCoefficient R E s x y := by
  obtain ⟨a, rfl⟩ := (simplexLambdaVertexEquiv R 1).surjective x
  obtain ⟨b, rfl⟩ := (simplexLambdaVertexEquiv R 1).surjective y
  exact simplexHAEdgeInverseFunctor_allHom_augmentation R E s a b

/-- 概要：元区間の全 Hom の増大表示は任意の単体的パラメータ変換を保つ。
方針：同じ全区間係数と Λ の元余モノイド射の増大保存を使う。
規約：全 Hom 複体射の等号。使われ方：元 end 辺の全 native 評価。 -/
lemma simplexHAEdgeBaseChange_augmentation (R : Type u) [CommRing R]
    (E : Type v) [DGCategory R E] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1)
    {A : SSet.{u}} (a : A ⟶ (Δ[1] : SSet.{u})) (x y : CubicalLambda R A) :
    (DGFunctor.comp (cubicalLambdaMap R a) (simplexHAInverseFunctor R s)).map x y =
      ε[(cubicalLambdaHomComonoid R A x y).X] ≫
        simplexHAEdgeObjectCoefficient R E s
          ((cubicalLambdaMap R a).obj x) ((cubicalLambdaMap R a).obj y) := by
  have h := simplexHAEdgeInverseFunctor_objects_augmentation R E s
    ((cubicalLambdaMap R a).obj x) ((cubicalLambdaMap R a).obj y)
  have hc := congrArg (fun f => (cubicalLambdaMap R a).map x y ≫ f) h
  apply hc.trans
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ simplexHAEdgeObjectCoefficient R E s
      ((cubicalLambdaMap R a).obj x) ((cubicalLambdaMap R a).obj y))
      (cubicalLambdaMapComonoid R a x y).isComonHom_hom.hom_counit)


/-- 概要：元区間辺との Λ tensor 全 Hom 作用は、同じ区間係数の単位挿入へ帰着する。
方針：任意パラメータの増大表示と元 Serre 対角の右増大則を合成する。
規約：元全 Hom・全基底変換を保持。使われ方：全 end 辺の native 同時評価。 -/
lemma cubicalLambdaFunctorPair_edgeBaseChange (R : Type u) [CommRing R]
    (C : Type w) [DGCategory R C] (E : Type v) [DGCategory R E]
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1) {A : SSet.{u}}
    (F : DGFunctor R (CubicalLambda R A) C) (a : A ⟶ (Δ[1] : SSet.{u}))
    (x y : CubicalLambda R A) :
    (cubicalLambdaFunctorPair R F
      (DGFunctor.comp (cubicalLambdaMap R a) (simplexHAInverseFunctor R s))).map x y =
      F.map x y ≫ (ρ_ _).inv ≫
        (𝟙 _ ⊗ₘ simplexHAEdgeObjectCoefficient R E s
          ((cubicalLambdaMap R a).obj x) ((cubicalLambdaMap R a).obj y)) := by
  have h := simplexHAEdgeBaseChange_augmentation R E s a x y
  have hc := congrArg (fun f =>
    Δ[(cubicalLambdaHomComonoid R A x y).X] ≫ (F.map x y ⊗ₘ f)) h
  apply hc.trans
  exact comonoidFunctorPair_right_point (cubicalLambdaHomComonoid R A x y) (F.map x y)
    (simplexHAEdgeObjectCoefficient R E s
      ((cubicalLambdaMap R a).obj x) ((cubicalLambdaMap R a).obj y))

end SerrePositivity.KST.SConstruction
