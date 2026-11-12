module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedPrismFixedSourceEndpoint

/-!
概要：始点射の頂点 fiber を固定始点パラメーターへの底変換として表示する。
方針：直積への射の第一成分を固定する普遍性を用いる。
規約：区間パラメーターの第二成分を保持する。
使われ方：同時の始点・終点制限の fiber ごとの同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 概要：直積への射の第一成分の fiber から固定第一成分への引き戻しへ移す。
方針：元の単体とその第二成分を組にする。
規約：単体集合は任意。
使われ方：始点の頂点 fiber の同定の順方向。 -/
def sourceVertexFiberToPullback {S M I : SSet.{u}} (p : S ⟶ M ⊗ I) (m : M _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ≫ fst M I) m ⟶ pullback p (lift (SSet.const m) (𝟙 I)) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p ≫ fst M I) m)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p ≫ fst M I) m ≫ p ≫ snd M I) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, lift_fst, SSet.comp_const]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp (p ≫ fst M I) m
      · simp only [Category.assoc, lift_snd, Category.comp_id])

/-- 概要：固定第一成分への引き戻しから第一成分の頂点 fiber へ移す。
方針：引き戻し条件の第一成分で fiber 条件を確認する。
規約：第二成分を忘れても元の単体は保つ。
使われ方：始点の頂点 fiber の同定の逆方向。 -/
def sourceVertexFiberFromPullback {S M I : SSet.{u}} (p : S ⟶ M ⊗ I) (m : M _⦋0⦌) :
    pullback p (lift (SSet.const m) (𝟙 I)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ≫ fst M I) m :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (p ≫ fst M I) m (pullback.fst _ _) (by
    rw [← Category.assoc, pullback.condition, Category.assoc, lift_fst, SSet.comp_const])

/-- 概要：第一成分の頂点 fiber と固定第一成分への底変換は厳密に同型。
方針：元の単体と第二成分を保つ二射が互いに逆であることを示す。
規約：quasicategory 性や fibration 性は不要。
使われ方：始点が動く全 lift 空間の実際の fiber の表示。 -/
def sourceVertexFiberPullbackIso {S M I : SSet.{u}} (p : S ⟶ M ⊗ I) (m : M _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ≫ fst M I) m ≅ pullback p (lift (SSet.const m) (𝟙 I)) where
  hom := sourceVertexFiberToPullback p m
  inv := sourceVertexFiberFromPullback p m
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (p ≫ fst M I) m
    simp only [Category.assoc, sourceVertexFiberFromPullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι,
      sourceVertexFiberToPullback, pullback.lift_fst, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, sourceVertexFiberToPullback, pullback.lift_fst,
        sourceVertexFiberFromPullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
    · simp only [Category.assoc, sourceVertexFiberToPullback, pullback.lift_snd,
        sourceVertexFiberFromPullback, Category.id_comp]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, ← Category.assoc, pullback.condition,
        Category.assoc, lift_snd, Category.comp_id]

/-- 概要：第一成分の fiber の同型は元の空間への包含を保つ。
方針：引き戻しへの標準持ち上げの第一射影を計算する。
規約：厳密な等式。
使われ方：fiber 上の終点評価の回収。 -/
lemma sourceVertexFiberPullbackIso_fst {S M I : SSet.{u}} (p : S ⟶ M ⊗ I)
    (m : M _⦋0⦌) :
    (sourceVertexFiberPullbackIso p m).hom ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p ≫ fst M I) m := pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
