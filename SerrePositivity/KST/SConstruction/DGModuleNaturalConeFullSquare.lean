module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeEndEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConePushout
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorLoopSquareCriterion

/-!
概要：元 cone の指定全四角形を native 全関手圏内の実押し出しとして保持する。
方針：同じ全 end 図式を全評価で写し、元実 cone の点ごとの普遍性を使用する。
規約：元両二胞体・元左包含原始元・元零角を保持。標的 Small 仮定なし。
使われ方：元逆回転との全 cofiber 図式比較と固定 ν の中央関手比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (D P : Type (u + 1))
  [DGCategory R D] [Small.{u} D] [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：元 cone 全 end 四角形の native 全関手族への同じ像。
方針：元全四角形を既存の全評価で写す。
規約：core へ制限しない。使われ方：全 cofiber 図式の実族。 -/
def dgModuleNaturalConeFullSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) :=
  dgModuleNaturalConeEndSquare R D F G η ≫
    dgFunctorNativeFullFamilyMap R P (RightModule R D)

/-- 概要：元全関手 cone 四角形の点評価は元実 cone 四角形そのもの。
方針：全評価と end 評価の厳密一致を使用する。
規約：四辺と両二胞体を保持。使われ方：点ごとの押し出し性。 -/
lemma dgModuleNaturalConeFullSquare_evaluation (x : P) :
    dgModuleNaturalConeFullSquare R D P F G η ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare R D (dgModuleNaturalConeArrow R D F G η x) := by
  rw [dgModuleNaturalConeFullSquare, Category.assoc, dgFunctorNativeFullFamilyMap_atPoint]
  exact dgModuleNaturalConeEndSquare_evaluation R D P F G η x

/-- 概要：元 cone の同じ全関手四角形は全関手圏内で実押し出し。
方針：全対象で元 dg cone 四角形を厳密回収し、既存の点ごとの余極限判定を使う。
規約：主経路の追加仮定なし。使われ方：同じ元実逆回転の普遍比較。 -/
lemma dgModuleNaturalConeFullSquare_isPushout :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgModuleNaturalConeFullSquare R D P F G η) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise
  intro k
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective k
  have he := dgModuleNaturalConeFullSquare_evaluation R D P F G η x
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare he).mpr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout R D _)

/-- 概要：全関手四角形の下二単体は同じ元 end 零化面の全評価像。
方針：元貼合せの下二単体を全関手評価で写す。
規約：元次数 −1 成分を保持。使われ方：指定上面・逆回転との同時照合。 -/
lemma dgModuleNaturalConeFullSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgModuleNaturalConeFullSquare R D P F G η =
      SSet.yonedaEquiv.symm
        ((dgFunctorNativeFullFamilyMap R P (RightModule R D)).app (Opposite.op ⦋2⦌)
          (dgModuleNaturalConeEndTriangle R D F G η)) := by
  rw [dgModuleNaturalConeFullSquare, ← Category.assoc, dgModuleNaturalConeEndSquare_lower]
  exact SSet.yonedaEquiv_symm_comp
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R P (RightModule R D)))
    (Y := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)))
    (n := SimplexCategory.mk 2) (dgModuleNaturalConeEndTriangle R D F G η)
    (dgFunctorNativeFullFamilyMap R P (RightModule R D))

/-- 概要：元全関手 cone 四角形の左上角は全関手圏で実零対象。
方針：同じ各点の元零加群を厳密回収し、点ごとの零対象判定を使う。
規約：同じ元零角を保持。使われ方：全 cofiber 列。 -/
lemma dgModuleNaturalConeFullSquare_zeroCorner :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgModuleNaturalConeFullSquare R D P F G η) 0 1) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_of_pointwise_evaluation
  intro k
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective k
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgModuleNaturalConeFullSquare R D P F G η ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) 0 1)
  have he := dgModuleNaturalConeFullSquare_evaluation R D P F G η x
  exact (congrArg (fun s => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s 0 1)) he).mpr
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTriangle R D (dgModuleNaturalConeArrow R D F G η x)).zero_corner

/-- 概要：元両面を持つ同じ全関手 cone 四角形を零角付き図式として保持する。
方針：同じ全四角形と実証した元零角を束ねる。
規約：四角形を選び直さない。使われ方：逆回転の全 cofiber 図式比較。 -/
def dgModuleNaturalConeFullZeroTriangle :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))) :=
  ⟨dgModuleNaturalConeFullSquare R D P F G η,
    dgModuleNaturalConeFullSquare_zeroCorner R D P F G η⟩

/-- 概要：元同じ全関手 cone 図式は実 cofiber 列である。
方針：同じ全押し出し性を零角付き図式へ使う。
規約：追加主仮定なし。使われ方：元逆回転と指定零化面の全比較。 -/
lemma dgModuleNaturalConeFullZeroTriangle_isCofiber :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence (dgModuleNaturalConeFullZeroTriangle R D P F G η) :=
  dgModuleNaturalConeFullSquare_isPushout R D P F G η

end SerrePositivity.KST.SConstruction
