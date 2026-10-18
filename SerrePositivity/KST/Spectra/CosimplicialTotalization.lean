module

public import SerrePositivity.KST.Spectra.SimplexTensorRelativeLatching
public import SerrePositivity.KST.Spectra.CosimplicialKanReplacement
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting
public import Mathlib.CategoryTheory.Enriched.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
概要：標準単体の重みを使う通常の余単体 Tot と実際の Reedy horn 充填。
方針：Tot を内部 Hom の end とし、horn をパラメーターにした Reedy 持ち上げを curry する。
規約：任意の図式で end を定義し、Kan 性には相対 matching の horn RLP を仮定する。
使われ方：Goerss–Jardine VIII §1、HTT A.3.3。L9e の通常の Tot の段ごとの模型。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open HomotopicalAlgebra SSet SSet.modelCategoryQuillen
open SerrePositivity.Reedy
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.CosimplicialTotalization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance totalizationSelfEnrichment : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  enrichedOrdinaryCategorySelf SSet.{u}

/-- 概要：余単体単体集合の標準単体を重みとする通常の Tot。
方針：標準単体から係数への単体的自然変換の end を取る。
規約：添字の simplex 圏は小さいままで、係数は任意の宇宙に置く。
使われ方：Goerss–Jardine VIII §1。通常の Tot の具体的な単体集合。 -/
def obj (X : CosimplicialObject SSet.{u}) : SSet.{u} :=
  Enriched.FunctorCategory.enrichedHom SSet.{u} SSet.stdSimplex X

/-- 概要：Tot の各次数の内部 Hom への射影。
方針：end の射影を使う。
規約：次数 j の標準単体全体上の族。
使われ方：Goerss–Jardine VIII §1。Tot の成分による比較。 -/
def π (X : CosimplicialObject SSet.{u}) (j : SimplexCategory) :
    obj X ⟶ (ihom (SSet.stdSimplex.obj j)).obj (X.obj j) :=
  Enriched.FunctorCategory.enrichedHomπ SSet.{u} SSet.stdSimplex X j

lemma condition (X : CosimplicialObject SSet.{u}) {i j : SimplexCategory} (g : i ⟶ j) :
    π X i ≫ (ihom (SSet.stdSimplex.obj i)).map (X.map g) =
      π X j ≫ (pre (SSet.stdSimplex.map g)).app (X.obj j) := by
  dsimp only [π, obj]
  simpa only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight] using
    Enriched.FunctorCategory.enrichedHom_condition SSet.{u} SSet.stdSimplex X g

/-- 概要：パラメーター付き標準単体の自然変換から Tot への射を作る。
方針：各成分を curry し、自然性を end の整合条件へ送る。
規約：パラメーターの Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。Tot の horn filler の構成。 -/
def lift {X : CosimplicialObject SSet.{u}} {A : SSet.{u}}
    (s : SimplexTensorBoundary.diagram A ⟶ X) : A ⟶ obj X :=
  end_.lift (fun j ↦ curry (s.app j)) (fun i j g ↦ by
    change curry (s.app i) ≫ eHomWhiskerLeft SSet.{u} _ (X.map g) =
      curry (s.app j) ≫ eHomWhiskerRight SSet.{u} (SSet.stdSimplex.map g) _
    rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
      enrichedOrdinaryCategorySelf_eHomWhiskerRight, ← curry_natural_right, curry_pre_app]
    apply congrArg curry
    exact (s.naturality g).symm)

@[reassoc (attr := simp)]
lemma lift_π {X : CosimplicialObject SSet.{u}} {A : SSet.{u}}
    (s : SimplexTensorBoundary.diagram A ⟶ X) (j : SimplexCategory) :
    lift s ≫ π X j = curry (s.app j) :=
  end_.lift_π _ _ j

/-- 概要：Tot への射をパラメーター付き標準単体の自然変換へ戻す。
方針：end の射影の後で各成分を uncurry する。
規約：元の射のパラメーターは任意の単体集合。
使われ方：Goerss–Jardine VIII §1。Reedy 持ち上げへ渡す horn の族。 -/
def uncurry {X : CosimplicialObject SSet.{u}} {A : SSet.{u}} (f : A ⟶ obj X) :
    SimplexTensorBoundary.diagram A ⟶ X where
  app j := MonoidalClosed.uncurry (f ≫ π X j)
  naturality i j g := by
    change (SSet.stdSimplex.map g ▷ A) ≫ MonoidalClosed.uncurry (f ≫ π X j) =
      MonoidalClosed.uncurry (f ≫ π X i) ≫ X.map g
    rw [← uncurry_pre_app, ← uncurry_natural_right]
    apply congrArg MonoidalClosed.uncurry
    rw [Category.assoc, Category.assoc, condition]

lemma lift_uncurry {X : CosimplicialObject SSet.{u}} {A : SSet.{u}} (f : A ⟶ obj X) :
    lift (uncurry f) = f := by
  apply end_.hom_ext
  intro j
  change lift (uncurry f) ≫ π X j = f ≫ π X j
  rw [lift_π]
  exact curry_uncurry _

lemma lift_pre {X : CosimplicialObject SSet.{u}} {A B : SSet.{u}} (i : A ⟶ B)
    (s : SimplexTensorBoundary.diagram B ⟶ X) :
    i ≫ lift s = lift (SimplexTensorBoundary.map i ≫ s) := by
  apply end_.hom_ext
  intro j
  change (i ≫ lift s) ≫ π X j = lift (SimplexTensorBoundary.map i ≫ s) ≫ π X j
  rw [Category.assoc, lift_π, lift_π]
  exact (curry_natural_left i (s.app j)).symm

/-- 概要：相対 matching が horn RLP な図式の通常の Tot は Kan。
方針：パラメーターの horn の Reedy anodyne 性と次数帰納の持ち上げを使う。
規約：置換前の図式にはこの相対条件が必要。一般の厳密極限の Kan 性を仮定しない。
使われ方：Goerss–Jardine VIII §1、HTT A.3.3。通常の Tot の実際の充填。 -/
lemma kanComplex (X : CosimplicialObject SSet.{u})
    (hX : reedyRight simplex J.rlp (CosimplicialKanReplacement.terminalArrows.obj X).hom) :
    KanComplex (obj X) := by
  let := CosimplicialHornFactorization.hornWeakFactorization.{u}
  apply (isFibrant_iff _).mpr
  apply (fibration_iff _).mpr
  intro A B i hi
  have hai : anodyneExtensions i := by
    rw [anodyneExtensions_eq_llp_rlp]
    exact MorphismProperty.le_llp_rlp J i hi
  have hir := SimplexTensorBoundary.map_reedy_anodyne i hai
  let : ∀ j, HasLiftingProperty
      (relativeLatchingMap simplex j (SimplexTensorBoundary.map i))
      (relativeMatchingMap simplex j (CosimplicialKanReplacement.terminalArrows.obj X).hom) :=
    fun j ↦ MorphismProperty.hasLiftingProperty_of_wfs _ _ (hir j) (hX j)
  let : HasLiftingProperty (SimplexTensorBoundary.map i)
      (CosimplicialKanReplacement.terminalArrows.obj X).hom := Lifting.hasLiftingProperty simplex
  refine ⟨fun {a b} sq ↦ ?_⟩
  let bottom : SimplexTensorBoundary.diagram B ⟶
      (Functor.const SimplexCategory).obj (⊤_ SSet.{u}) :=
    { app j := terminal.from _
      naturality _ _ _ := by simp }
  let q : CommSq (uncurry a) (SimplexTensorBoundary.map i)
      (CosimplicialKanReplacement.terminalArrows.obj X).hom bottom :=
    ⟨by
      apply NatTrans.ext
      funext j
      exact terminal.hom_ext _ _⟩
  refine ⟨⟨{ l := lift q.lift, fac_left := ?_, fac_right := by subsingleton }⟩⟩
  rw [lift_pre, q.fac_left, lift_uncurry]

end

end SerrePositivity.KST.Spectra.CosimplicialTotalization
