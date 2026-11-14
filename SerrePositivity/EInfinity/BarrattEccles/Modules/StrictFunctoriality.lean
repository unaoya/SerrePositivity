module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRestrictionComparison
public import SerrePositivity.EInfinity.Modules.DGRestrictionLaws

/-!
# 厳密 BE 加群の同じ拡大・制限の恒等と合成

概要：HA §4.2.3 の実拡大・制限の法則を全関手同型として構成する。
方針：制限の実出力解像度の比較を使い、拡大の比較は同じ随伴の一意性で得る。
規約：高次単体を含む全族の構成は別であり、孤立した比較で代用しない。
使われ方：BE 加群族に渡す恒等・合成の指定比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (A : Type u) [CommRing A]

/-- 概要：同じ dg 代数射の恒等則（HA §4.2.3）。
方針：一対象の全 Hom 上で照合。規約：同じ carrier。使われ方：制限の恒等比較。 -/
lemma algebraMap_id (B : Mon (Complex A)) :
    dgAlgebraMap A (𝟙 B) = DGFunctor.id (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory A B) := by
  rw [dgAlgebraMap, ← DGFunctor.op_id]
  congr 1

/-- 概要：同じ dg 代数射の合成則（HA §4.2.3）。
方針：一対象の全 Hom 上で照合。規約：同じ carrier。使われ方：制限の合成比較。 -/
lemma algebraMap_comp {B C T : Mon (Complex A)} (f : B ⟶ C) (g : C ⟶ T) :
    dgAlgebraMap A (f ≫ g) = (dgAlgebraMap A f).comp (dgAlgebraMap A g) := by
  rw [dgAlgebraMap, dgAlgebraMap, dgAlgebraMap, ← DGFunctor.op_comp]
  congr 1

/-- 概要：厳密 BE 底の恒等制限の全関手比較（HA §4.2.3）。
方針：同じ dg 代数の恒等則と解像度の retract 比較を使う。
規約：指定の restriction。使われ方：族の単位法則。 -/
def strictModuleRestrict_idIso (X : (operad A).Algebra) :
    FunctorIso (strictModuleRestrict (𝟙 X)) (𝟙 (strictModuleInfinity A X)) := by
  change FunctorIso (resolvedRestriction A _ _ (dgAlgebraMap A ((assocForget A).map (𝟙 X)))) _
  rw [CategoryTheory.Functor.map_id, algebraMap_id]
  exact resolvedRestriction_idIso A _

/-- 概要：厳密 BE 底の反変制限の合成比較（HA §4.2.3）。
方針：同じ dg 代数射の合成則を実出力解像度の比較へ送る。
規約：全関手同型。使われ方：族の辺の合成。 -/
def strictModuleRestrict_compIso {X Y Z : (operad A).Algebra} (f : X ⟶ Y) (g : Y ⟶ Z) :
    FunctorIso (strictModuleRestrict g ≫ strictModuleRestrict f)
      (strictModuleRestrict (f ≫ g)) := by
  change FunctorIso
    (resolvedRestriction A _ _ (dgAlgebraMap A ((assocForget A).map g)) ≫
      resolvedRestriction A _ _ (dgAlgebraMap A ((assocForget A).map f)))
    (resolvedRestriction A _ _ (dgAlgebraMap A ((assocForget A).map (f ≫ g))))
  rw [CategoryTheory.Functor.map_comp, algebraMap_comp]
  exact resolvedRestriction_compIso A _ _ _ _ _

/-- 概要：厳密 BE 底の恒等拡大の全関手比較（HA §4.2.3）。
方針：恒等制限へ移した同じ随伴と恒等随伴を比較する。
規約：元の実拡大。使われ方：族の単位法則。 -/
def strictModuleExtend_idIso (X : (operad A).Algebra) :
    FunctorIso (strictModuleExtend (𝟙 X)) (𝟙 (strictModuleInfinity A X)) :=
  (qcatAdjunctionChangeRight (strictModuleAdjunction (𝟙 X))
    (strictModuleRestrict_idIso A X)).leftAdjointFunctorIso (QCatAdjunction.refl _)

/-- 概要：厳密 BE 底の拡大の合成比較（HA §4.2.3）。
方針：随伴の合成と制限の合成比較から左随伴の一意性を使う。
規約：全関手同型。使われ方：族の辺の合成。 -/
def strictModuleExtend_compIso {X Y Z : (operad A).Algebra} (f : X ⟶ Y) (g : Y ⟶ Z) :
    FunctorIso (strictModuleExtend (f ≫ g))
      (strictModuleExtend f ≫ strictModuleExtend g) :=
  (strictModuleAdjunction (f ≫ g)).leftAdjointFunctorIso
    (qcatAdjunctionChangeRight ((strictModuleAdjunction f).comp (strictModuleAdjunction g))
      (strictModuleRestrict_compIso A f g))

end SerrePositivity.EInfinity.BarrattEccles
