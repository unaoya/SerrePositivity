module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleProbeNativeHom
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentPinchedTransport

/-!
# 同じ局所化比較 K の元の probe 上の Hom 射

概要：M10 の K の誘導射を、指定半自由端点と元の dg Hom の座標へ運ぶ。
方針：元の全 probe 包含・同じ源の三角比較・同じ解像度の retract 成分を合成する。
規約：HA §1.3.4、1.3.1.13。K も端点成分も選び直さない。
使われ方：具体的 frame Hom の比較と同じ誘導射の完全忠実性の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：元の全 probe 包含を同じ相対圏の宇宙表示へ送る。
方針：既存の全包含の後に同じ ULiftHom 関手を合成する。
規約：HA §1.3.4、全 probe 射。使われ方：同じ K の元の入力。 -/
def strictRawModuleProbeRelativeFunctor (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (strictRawModuleRelativeCategory A X).category :=
  strictRawModuleProbeFunctor A X ⋙
    ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)

/-- 概要：同じ元の probe の標準局所化頂点。
方針：既存の同じ頂点同値を元の全包含の値に適用する。
規約：HA §1.3.4、同じ頂点。使われ方：K の同じ Hom 射の始域端点。 -/
def strictRawModuleProbeLocalizationVertex (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve (strictRawModuleRelativeCategory A X)) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv (strictRawModuleRelativeCategory A X)
    (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory (strictRawModuleRelativeCategory A X) from
      (strictRawModuleProbeRelativeFunctor A X).obj P)

/-- 概要：元の probe の同じ通常源の値を指定半自由頂点へ戻す。
方針：同じ全解像度 retract 同型の成分と源の頂点式を使う。
規約：HA 1.3.1.13、同じ成分。使われ方：K の Hom 射の指定端点。 -/
def strictRawModuleProbeSourceVertexIso (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    VertexIso
      ((strictRawModuleSource A X).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((strictRawModuleProbeRelativeFunctor A X).obj P)))
      (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A) P)) := by
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  have e := (dgModuleResolutionRetractIso A D).app
    (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A) P))
  change VertexIso
    ((moduleResolution A D).app (op ⦋0⦌)
      ((DifferentialGradedCategories.Functor.map (semifreeInclusion A D)).app (op ⦋0⦌)
        (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A) P))))
    (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A) P)) at e
  rw [dgFunctorNerve_vertex] at e
  rw [strictRawModuleSource_vertex]
  exact e

/-- 概要：同じ K の標準 probe 頂点での値は指定半自由頂点と同じ成分で比較される。
方針：同じ全源の三角成分と同じ retract 成分を合成する。
規約：HA §1.3.4、元の K。使われ方：実 pinched Hom の端点輸送。 -/
def strictRawModuleProbeComparisonVertexIso (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    VertexIso
      ((strictRawModuleComparison A X).app (op ⦋0⦌) (strictRawModuleProbeLocalizationVertex A X P))
      (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A) P)) :=
  strictRawModuleComparison_vertexIso A X ((strictRawModuleProbeRelativeFunctor A X).obj P) ≪≫
    strictRawModuleProbeSourceVertexIso A X P

/-- 概要：同じ K の pinched Hom 射を指定半自由端点で表す。
方針：元の誘導射の後に同じ二つの端点成分による同値を合成する。
規約：HA §1.3.4、元の全単体の射。使われ方：完全忠実性で検証する同じ写像。 -/
def strictRawModuleProbeComparisonPinchedMap (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve (strictRawModuleRelativeCategory A X))
      (strictRawModuleProbeLocalizationVertex A X P) (strictRawModuleProbeLocalizationVertex A X Q) ⟶
      PinchedHom.pinchedHom A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q) :=
  pinchedHomMap (strictRawModuleComparison A X) _ _ ≫
    (pinchedEndpointEquivalence (strictRawModuleProbeComparisonVertexIso A X P)
      (strictRawModuleProbeComparisonVertexIso A X Q)).hom

/-- 概要：同じ K の Hom 射を元の dg Hom の実 Dold–Kan 座標へ戻す。
方針：指定端点での同じ実 pinched 同型の逆を後合成する。
規約：HA 1.3.1.13、同じ射。使われ方：frame Hom 比較との照合の対象。 -/
def strictRawModuleProbeComparisonDoldKanMap (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve (strictRawModuleRelativeCategory A X))
      (strictRawModuleProbeLocalizationVertex A X P) (strictRawModuleProbeLocalizationVertex A X Q) ⟶
      SSet.uliftFunctor.{u + 1, u}.obj
        (((strictRawModuleProbeDoldKanHom A X).obj (op P)).obj
          ((strictRawModuleProbeFunctor A X).obj Q)) :=
  strictRawModuleProbeComparisonPinchedMap A X P Q ≫ (strictRawModuleProbeNativeHomIso A X P Q).inv

/-- 概要：同じ座標での K の Hom 射は元の指定 pinched Hom 射を回収する。
方針：同じ端点同型の逆・順の合成を相殺する。
規約：HA 1.3.1.13、全単体の等式。使われ方：射を変えない完全忠実性の照合。 -/
lemma strictRawModuleProbeComparisonDoldKanMap_triangle (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    strictRawModuleProbeComparisonDoldKanMap A X P Q ≫ (strictRawModuleProbeNativeHomIso A X P Q).hom =
      strictRawModuleProbeComparisonPinchedMap A X P Q := by
  dsimp only [strictRawModuleProbeComparisonDoldKanMap]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.EInfinity.BarrattEccles
