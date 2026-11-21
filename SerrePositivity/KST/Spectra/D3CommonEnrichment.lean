module

public import SerrePositivity.KST.Spectra.D3CommonHomLaws
public import SerrePositivity.CategoryTheory.Enriched.BaseChange

/-!
概要：比較射を保持する共通 Hom の局所 Kan な単体的圏と実射影関手。
方針：二つの実射影で検証した厳密単位・合成・結合律を豊穣構造へ束ねる。
規約：元の全左右因子と比較を保持する。実 loop 図式との接続は未完。
使われ方：d3b② の比較を含む全 Hom の coherent nerve。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance commonEnrichmentSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 比較を含む同じ全 Hom は元の Kan Hom への実自明射影から Kan。 -/
instance commonHom_kanComplex (X Y : OmegaSpectrum.{u}) : KanComplex (commonHom X Y) := by
  let : HomotopicalAlgebra.Fibration (commonBaseMap X Y) :=
    (SSet.modelCategoryQuillen.fibration_iff _).2
      (fun _ _ j hj ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := commonBaseMap X Y)) j
        (SSet.modelCategoryQuillen.J_le_monomorphisms j hj))
  change HomotopicalAlgebra.Fibration (terminal.from (commonHom X Y))
  rw [show terminal.from (commonHom X Y) = commonBaseMap X Y ≫
    terminal.from (fullCompatibleSpace X Y) from terminal.hom_ext _ _]
  infer_instance

/-- 比較を含む共通解像の対象。元の BF 対象を同じまま包む。 -/
structure CommonObject where
  /-- 元の BF 対象。 -/
  val : OmegaSpectrum.{u}

/-- 二段包含・比較を保持する全 Hom の厳密な豊穣構造。 -/
instance commonSimplicialEnrichedCategory : EnrichedCategory SSet.{u} CommonObject where
  Hom X Y := commonHom X.val Y.val
  id X := commonIdentity X.val
  comp X Y Z := commonComposition X.val Y.val Z.val
  id_comp X Y := commonIdentity_composition X.val Y.val
  comp_id X Y := commonComposition_identity X.val Y.val
  assoc W X Y Z := commonComposition_assoc W.val X.val Y.val Z.val

/-- 単位からの豊穣射を通常射とする圏構造。 -/
instance commonCategory : Category.{u} CommonObject :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} CommonObject))

/-- 元の全 Hom の対応を備えた単体的圏。 -/
instance commonSimplicialCategory : SimplicialCategory CommonObject where
  homEquiv := Equiv.refl _
  homEquiv_id X := ForgetEnrichment.homTo_id (W := SSet.{u}) (C := CommonObject) X
  homEquiv_comp f g := ForgetEnrichment.homTo_comp (W := SSet.{u}) (C := CommonObject) f g

/-- 同じ共通解像の全豊穣 Hom は Kan。 -/
instance commonHomSimplicial_kanComplex (X Y : CommonObject) :
    KanComplex (SimplicialCategory.sHom X Y) := commonHom_kanComplex X.val Y.val

/-- 元の FullCompatible 解像への実豊穣射影。 -/
def commonBaseEnriched : EnrichedFunctor SSet.{u} CommonObject FullObject where
  obj X := ⟨X.val⟩
  map X Y := commonBaseMap X.val Y.val
  map_id X := commonIdentity_base X.val
  map_comp X Y Z := commonComposition_base X.val Y.val Z.val

/-- 共通 BF 対象への実豊穣射影。 -/
def commonRefinedEnriched : EnrichedFunctor SSet.{u} CommonObject OmegaSpectrum.{u} where
  obj X := commonRefinement X.val
  map X Y := commonRefinedMap X.val Y.val
  map_id X := commonIdentity_refined X.val
  map_comp X Y Z := commonComposition_refined X.val Y.val Z.val

/-- 同じ共通解像から元の BF 対象と全 Hom を回収する。 -/
def commonOriginalEnriched : EnrichedFunctor SSet.{u} CommonObject OmegaSpectrum.{u} :=
  commonBaseEnriched.comp SSet fullOriginalEnriched

/-- 同じ共通解像から元の相対 BF 対象と全 Hom を回収する。 -/
def commonMiddleEnriched : EnrichedFunctor SSet.{u} CommonObject OmegaSpectrum.{u} :=
  commonBaseEnriched.comp SSet fullReplacedEnriched

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
