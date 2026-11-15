module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleDerivedSource
public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictUnderlyingComparison
public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRegularSection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.ClosedNerveFunctorNaturality

/-!
# 同じ通常加群の源と native 制限・台・単位の比較

概要：HA §4.2.3 の元の全制限を、同じ通常加群の源の前後で比較する。
方針：閉零源の全自然性と、擬同型を保つ制限の同じ出力分解比較を貼る。
規約：元の制限・台の評価・正則加群を保持する。
使われ方：M10/C02 の相対局所化と半自由 fiber の比較の指定源での照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable (A : Type u) [CommRing A]

/-- 概要：同じ通常加群の dg 源は元の制限に全単体で自然（HA §4.2.3）。
方針：同じ閉零列の全 dg 関手自然性と Hom の持ち上げを戻す計算を使う。
規約：全単体写像の等式。使われ方：指定半自由分解への自然性。 -/
lemma strictRawModuleDGSource_restrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    nerveMap (strictRawModuleRestrictRelative f).functor ≫ strictRawModuleDGSource A X =
      strictRawModuleDGSource A Y ≫
        N (dgModuleRestriction A (dgAlgebraCategory A ((assocForget A).obj X))
          (dgAlgebraCategory A ((assocForget A).obj Y)) (dgAlgebraMap A ((assocForget A).map f)).op) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change closedNerveSimplex
    ((s ⋙ (strictRawModuleRestrictRelative f).functor) ⋙
      ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)) =
    (closedNerveSimplex (s ⋙ ULiftHom.down.{u,u+1,u+1}
      (C := strictRawModuleCategory A Y))).map
      (dgModuleRestriction A (dgAlgebraCategory A ((assocForget A).obj X))
        (dgAlgebraCategory A ((assocForget A).obj Y)) (dgAlgebraMap A ((assocForget A).map f)).op)
  rw [dgFunctor_closedNerveSimplex, dgModuleRestriction_onClosed_eq]
  rfl

/-- 概要：同じ全加群の分解は元の制限と全関手同型で可換（HA §4.2.3）。
方針：制限の擬同型保存で二段分解を一段へ比較し、入力の前合成則を使う。
規約：制限の半自由性保存は要求しない。使われ方：通常の源の制限との比較。 -/
def strictRawResolvedRestrictionIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj Y)) ≫ strictModuleRestrict f)
      (N (dgModuleRestriction A (dgAlgebraCategory A ((assocForget A).obj X))
        (dgAlgebraCategory A ((assocForget A).obj Y)) (dgAlgebraMap A ((assocForget A).map f)).op) ≫
        moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))) := by
  let DX := dgAlgebraCategory A ((assocForget A).obj X)
  let DY := dgAlgebraCategory A ((assocForget A).obj Y)
  let RF := dgModuleRestriction A DX DY (dgAlgebraMap A ((assocForget A).map f)).op
  have e := dgModuleResolvedInfinity_compositionIso A (RightModule A DY) DY DX
    (DGFunctor.id (RightModule A DY)) RF (fun T => by
      rw [dgModuleRestriction_map]
      exact moduleRestriction_quasiIso A DX DY (dgAlgebraMap A ((assocForget A).map f)).op
        T.augmentation T.quasiIso)
  have h0 : (DGFunctor.id (RightModule A DY)).comp RF = RF := by
    apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
    intro M T
    simp only [EnrichedFunctor.comp_map, EnrichedFunctor.id_map, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  rw [h0] at e
  have p := dgModuleResolvedInfinity_precompIso A (RightModule A DY) (RightModule A DX) DX
    RF (DGFunctor.id (RightModule A DX))
  have h1 : RF.comp (DGFunctor.id (RightModule A DX)) = RF := by
    apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
    intro M T
    simp only [EnrichedFunctor.comp_map, EnrichedFunctor.id_map, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  rw [h1] at p
  exact e ≪≫ p

/-- 概要：同じ通常加群の源は native 制限に全関手間で自然（HA §4.2.3）。
方針：元の dg 源の厳密な自然性と同じ全分解の比較を貼る。
規約：元の全関手を保持する。使われ方：M10/C02 の同じ制限の回収。 -/
def strictRawModuleSource_restrictIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (nerveMap (strictRawModuleRestrictRelative f).functor ≫ strictRawModuleSource A X)
      (strictRawModuleSource A Y ≫ strictModuleRestrict f) := by
  have e := (strictRawResolvedRestrictionIso A f).precomp (strictRawModuleDGSource A Y)
  change FunctorIso (strictRawModuleSource A Y ≫ strictModuleRestrict f)
    ((strictRawModuleDGSource A Y ≫
      N (dgModuleRestriction A (dgAlgebraCategory A ((assocForget A).obj X))
        (dgAlgebraCategory A ((assocForget A).obj Y)) (dgAlgebraMap A ((assocForget A).map f)).op)) ≫
      moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))) at e
  rw [← strictRawModuleDGSource_restrict A f] at e
  simpa only [strictRawModuleSource, Category.assoc] using e.symm

/-- 概要：同じ通常加群の源の台は元の同じ複体の実評価（HA §4.2.1）。
方針：同じ分解と台の全比較を元の通常 dg 源で前合成する。
規約：元の評価関手と一点比較。使われ方：M10/C02 の同じ U の照合。 -/
def strictRawModuleSource_underlyingIso (X : (operad A).Algebra) :
    FunctorIso (strictRawModuleSource A X ≫ strictModuleUnderlying A X)
      (strictRawModuleDGSource A X ≫
        N (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
          (Opposite.op DGAlgebraPoint.star)) ≫
        dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
          (DiagramComparison.semifreePointEquivalence A).hom) := by
  simpa only [strictRawModuleSource, Category.assoc] using
    (strictModuleResolvedUnderlyingIso A X).precomp (strictRawModuleDGSource A X)

/-- 概要：同じ通常加群の源は元の正則加群を指定単位へ送る（HA §4.2.1）。
方針：同じ源の頂点の式に元の正則加群を代入する。
規約：元の正則加群を保持する。使われ方：M10/C02 の同じ単位の照合。 -/
lemma strictRawModuleSource_regular (X : (operad A).Algebra) :
    (strictRawModuleSource A X).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ ((ULiftHom.up.{u,u+1,u+1}
        (C := strictRawModuleCategory A X)).obj (strictRawRegularObject A X).fiber)) =
      strictModuleUnit A X := by
  rw [strictRawModuleSource_vertex]
  rfl

attribute [cite HA "4.2.3" (partial := component)
  "同じ通常加群の源と指定 native 制限の全関手自然性。全族の cocartesian 性は含まない。"]
  strictRawModuleDGSource_restrict strictRawResolvedRestrictionIso strictRawModuleSource_restrictIso
attribute [cite HA "4.2.1" (partial := component)
  "同じ通常加群の源の台と正則加群を元の指定 U・単位へ照合する法則。"]
  strictRawModuleSource_underlyingIso strictRawModuleSource_regular

end SerrePositivity.EInfinity.BarrattEccles
