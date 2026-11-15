module

public import SerrePositivity.EInfinity.Modules.CotensorSimplices
public import SerrePositivity.EInfinity.AlexanderWhitney.SimplexCounitContraction
public import SerrePositivity.EInfinity.HomHomotopy

/-!
# 標準単体の余単位による cotensor の比較

概要：M10 の同じ simplicial cotensor に、単位係数からの自然な弱同値を与える。
方針：既存の AW 余単位の実ホモトピー逆を Hom 前合成へ送る。
規約：HA §1.3.4。単位係数 cotensor と元の加群の同定は別に行う。
使われ方：具体的な right frame の homotopically constant 条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：係数の実鎖ホモトピー同値の前合成は元の加群の擬同型。
方針：各評価で既存の Hom ホモトピー同値を使う。
規約：HA §1.3.4、任意の標的。使われ方：単体余単位の弱同値性。 -/
lemma moduleCotensorPreMap_quasiIso {K L : Complex A} (f : K ⟶ L)
    (hf : HomologicalComplex.homotopyEquivalences (ModuleCat A) (.up ℤ) f)
    (M : ModuleCategory A D) :
    moduleQuasiIso A D (moduleCotensorPreMap A D f M) := by
  intro x
  rw [moduleCotensorPreMap_eval]
  obtain ⟨e, rfl⟩ := hf
  exact (homPrecomposeHomotopyEquiv e ((moduleEvaluation A D x).obj M)).quasiIso_hom

/-- 概要：同じ AW 余単位は単位 cotensor の定数図式から全単体への射を与える。
方針：元の余単位の自然性と前合成の合成則を使う。
規約：HA §1.3.4、面・退化を含む。使われ方：frame の定数比較。 -/
def moduleCotensorCounitNat (M : ModuleCategory A D) :
    (Functor.const SimplexCategoryᵒᵖ).obj (moduleCotensor A D (𝟙_ (Complex A)) M) ⟶
      moduleCotensorSimplices A D M where
  app n := moduleCotensorPreMap A D
    (AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n.unop)) M
  naturality n m f := by
    change 𝟙 _ ≫ _ = _ ≫ _
    rw [Category.id_comp]
    apply moduleMorphism_ext
    intro x
    change (moduleEvaluation A D x).map (moduleCotensorPreMap A D _ M) =
      (moduleEvaluation A D x).map
        (moduleCotensorPreMap A D _ M ≫ (moduleCotensorSimplices A D M).map f)
    rw [CategoryTheory.Functor.map_comp, moduleCotensorPreMap_eval,
      moduleCotensorPreMap_eval, moduleCotensorSimplices_map_eval,
      ← homPrecompose_comp, AlexanderWhitney.cochainCounit_natural]

/-- 概要：同じ余単位比較の全ての次数成分は元の加群の擬同型。
方針：標準単体の実収縮を係数前合成へ移す。
規約：HA §1.3.4、追加のモデル仮定なし。使われ方：定数比較の弱同値性。 -/
lemma moduleCotensorCounitNat_weak (M : ModuleCategory A D) (n : SimplexCategoryᵒᵖ) :
    moduleQuasiIso A D ((moduleCotensorCounitNat A D M).app n) :=
  moduleCotensorPreMap_quasiIso A D _
    (AlexanderWhitney.cochainCounit_stdSimplex_homotopyEquivalence A n.unop) M

/-- 概要：同じ余単位比較は全ての元の加群射について自然。
方針：同じ係数前合成の自然変換を各単体で使う。
規約：HA §1.3.4、全標的の族。使われ方：frame 比較の自然性。 -/
def moduleCotensorCounitFamily :
    moduleCotensorFunctor A D (𝟙_ (Complex A)) ⋙ Functor.const SimplexCategoryᵒᵖ ⟶
      moduleCotensorSimplicesFunctor A D where
  app := moduleCotensorCounitNat A D
  naturality M N g := by
    apply NatTrans.ext
    funext n
    exact (moduleCotensorPreNat A D
      (AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n.unop))).naturality g

/-- 概要：同じ simplicial cotensor の全ての面・退化は元の擬同型。
方針：同じ余単位の自然性と擬同型の二つから三つを使う。
規約：HA §1.3.4、Reedy fibrancy は別。使われ方：homotopically constant 条件。 -/
lemma moduleCotensorSimplices_maps_weak (M : ModuleCategory A D)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    moduleQuasiIso A D ((moduleCotensorSimplices A D M).map f) := by
  intro x
  let E := moduleEvaluation A D x
  have hn := moduleCotensorCounitNat_weak A D M n x
  have hm := moduleCotensorCounitNat_weak A D M m x
  have h := (moduleCotensorCounitNat A D M).naturality f
  change 𝟙 _ ≫ _ = _ ≫ _ at h
  rw [Category.id_comp] at h
  have hc : E.map ((moduleCotensorCounitNat A D M).app n) ≫
      E.map ((moduleCotensorSimplices A D M).map f) =
      E.map ((moduleCotensorCounitNat A D M).app m) := by
    rw [← E.map_comp, ← h]
  have : QuasiIso (E.map ((moduleCotensorCounitNat A D M).app n) ≫
      E.map ((moduleCotensorSimplices A D M).map f)) := by
    rw [hc]
    exact hm
  exact quasiIso_of_comp_left (E.map ((moduleCotensorCounitNat A D M).app n)) _

end SerrePositivity.EInfinity.Modules
