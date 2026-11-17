module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRawCartesian

/-!
# 同じ正則 BE 加群の全圏への section

概要：HA §4.2.3 の正則加群を、変わる底上の同じ全圏の section として組み立てる。
方針：元の表現可能加群と同じ Hom 鎖写像の制限比較を使う。
規約：同じ台の代数射を保つ。半自由 fiber との比較は別に検証する。
使われ方：native な全加群族の単位の section。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
attribute [local implicit_reducible] strictRawModuleRestrictionPseudofunctor
variable (A : Type u) [CommRing A]

/-- 概要：同じ底と台の成分で全加群の射を検出する（HA §4.2.3）。
方針：底を同定した後に唯一点の忠実な評価を使う。
規約：元の全圏の射。使われ方：正則加群の section の関手則。 -/
lemma strictRawModuleTotal_hom_ext {M T : strictRawModuleTotal A} {f g : M ⟶ T}
    (hb : (strictRawModuleProjection A).map f = (strictRawModuleProjection A).map g)
    (hv : (strictRawModuleTotalForget A).map f = (strictRawModuleTotalForget A).map g) : f = g := by
  rcases f with ⟨f, φ⟩
  rcases g with ⟨g, ψ⟩
  change f = g at hb
  subst g
  have hφ : φ = ψ := strictRawModuleHom_ext (X := M.base) hv
  subst ψ
  rfl

/-- 概要：同じ厳密底の正則右加群を全圏に載せる（HA §4.2.1）。
方針：唯一点の表現可能加群を使う。
規約：元の同じ dg 代数。使われ方：単位の section の対象。 -/
def strictRawRegularObject (X : (operad A).Algebra) : strictRawModuleTotal A where
  base := X
  fiber := ForgetEnrichment.of (Complex A)
    (C := RightModule A (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory A ((assocForget A).obj X)))
    (representable A (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star))

/-- 概要：同じ正則加群の台は元の BE carrier（HA §4.2.1）。
方針：唯一点の表現可能加群を評価する。
規約：複体の厳密な等式。使われ方：単位の台の比較。 -/
lemma strictRawRegularObject_underlying (X : (operad A).Algebra) :
    (strictRawModuleTotalForget A).obj (strictRawRegularObject A X) = X.carrier := rfl

/-- 概要：元の BE 射が同じ正則加群間に与える射（HA §4.2.3）。
方針：元の dg 代数射の全 Hom 自然な表現可能制限比較を使う。
規約：同じ係数射。使われ方：単位の section の射。 -/
def strictRawRegularMap {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawRegularObject A X ⟶ strictRawRegularObject A Y where
  base := f
  fiber := representableRestrictionMap A _ _ (dgAlgebraMap A ((assocForget A).map f))
    (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star)

/-- 概要：同じ正則加群間の射の台は元の代数射（HA §4.2.3）。
方針：元の表現可能制限比較の評価公式を使う。
規約：同じ鎖写像。使われ方：section の準同型保存。 -/
lemma strictRawRegularMap_underlying {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    (strictRawModuleTotalForget A).map (strictRawRegularMap A f) = f.hom :=
  representableRestrictionMap_eval A _ _ (dgAlgebraMap A ((assocForget A).map f)) _ _

/-- 概要：同じ正則加群の通常の section（HA §4.2.3）。
方針：底と台の同じ二成分で関手則を照合する。
規約：元の代数・正則加群・係数射を保つ。使われ方：単位の全族。 -/
def strictRawModuleUnitSection : (operad A).Algebra ⥤ strictRawModuleTotal A where
  obj := strictRawRegularObject A
  map := strictRawRegularMap A
  map_id X := by
    refine strictRawModuleTotal_hom_ext A ?_ ?_
    · rfl
    rw [strictRawRegularMap_underlying, CategoryTheory.Functor.map_id]
    all_goals rfl
  map_comp f g := by
    refine strictRawModuleTotal_hom_ext A ?_ ?_
    · rfl
    simp only [CategoryTheory.Functor.map_comp, strictRawRegularMap_underlying]
    all_goals rfl

/-- 概要：正則加群の section の射影は同じ恒等関手（HA §4.2.3）。
方針：元の底の成分を評価する。
規約：全関手の等式。使われ方：単位の底の指定。 -/
lemma strictRawModuleUnitSection_projection :
    strictRawModuleUnitSection A ⋙ strictRawModuleProjection A = 𝟭 (operad A).Algebra := rfl

/-- 概要：同じ正則加群の section は相対関手（HA §4.2.3）。
方針：台の射が元の準同型そのものであることを使う。
規約：同じ全圏の準同型条件。使われ方：単位の section の局所化。 -/
def strictRawModuleUnitSectionRelative : algebraRelativeCategory A ⟶ strictRawModuleTotalRelative A where
  functor := ULiftHom.down.{u,u+1,u+1} (C := (operad A).Algebra) ⋙
    strictRawModuleUnitSection A ⋙ ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)
  map := by
    intro X Y f hf
    constructor
    · exact hf
    · change QuasiIso ((strictRawModuleTotalForget A).map (strictRawRegularMap A f.down))
      rw [strictRawRegularMap_underlying]
      change @_root_.HomotopicalAlgebra.weakEquivalences (operad A).Algebra _
        (modelCategory A).categoryWithWeakEquivalences _ _ f.down at hf
      rw [modelCategory_weakEquivalences] at hf
      exact hf

/-- 概要：相対 section の射影は同じ相対恒等関手（HA §4.2.3）。
方針：元の全ての代数射で底の成分を評価する。
規約：相対関手の厳密な等式。使われ方：native section の射影比較。 -/
lemma strictRawModuleUnitSectionRelative_projection :
    strictRawModuleUnitSectionRelative A ≫ strictRawModuleTotalProjectionRelative A =
      𝟙 (algebraRelativeCategory A) := by
  apply relativeFunctor_ext
  rfl

/-- 概要：同じ CAlg から全加群の局所化への正則加群の実関手（HA §4.2.3）。
方針：同じ cofibrant 包含と相対 section を局所化する。
規約：全単体を持つ実写像。使われ方：全加群族の単位。 -/
def moduleUnitSection : CAlg_R A ⟶ moduleTotalInfinity A :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (cofibrantToAlgebraDKRelative A ≫ strictRawModuleUnitSectionRelative A)

/-- 概要：正則加群の実関手の射影は同じ包含・置換の局所化（HA §4.2.3）。
方針：相対 section の厳密な射影式と局所化の合成則を使う。
規約：全単体での等式。使われ方：元の cofibrant 比較による section の回収。 -/
lemma moduleUnitSection_projection :
    moduleUnitSection A ≫ moduleTotalProjection A =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (cofibrantToAlgebraDKRelative A ≫ algebraToCofibrantDKRelative A) := by
  rw [moduleUnitSection, moduleTotalProjection, ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_comp]
  rw [← Category.assoc, Category.assoc (cofibrantToAlgebraDKRelative A),
    strictRawModuleUnitSectionRelative_projection, Category.comp_id]

end SerrePositivity.EInfinity.BarrattEccles
