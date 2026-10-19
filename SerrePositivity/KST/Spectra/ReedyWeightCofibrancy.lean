module

public import SerrePositivity.KST.Spectra.LastVertexWeightProjections
public import SerrePositivity.KST.Spectra.FreeInterval
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.WeakFactorizationSystem

/-!
概要：終頂点比較の両重みと二射影の中間重みは実際に Reedy cofibrant。
方針：境界の弱因子分解系で Reedy 左類の合成閉性を示し、anodyne な置換単位を合成する。
規約：cofibrancy は相対 latching の単射性で述べる。
使われ方：Goerss–Jardine VII §4。重みの比較の相対 cylinder に必要な左持ち上げ性。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.ReedyWeightCofibrancy
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reedy の単射左類は全単射 RLP の相対 matching 右類の LLP。 -/
lemma left_eq_llp : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) =
    (reedyRight simplex (MorphismProperty.monomorphisms SSet.{u}).rlp).llp := by
  let := CosimplicialRelativeWhitehead.boundaryWeakFactorization.{u}
  let := weakFactorizationSystem simplex (MorphismProperty.monomorphisms SSet.{u})
    (MorphismProperty.monomorphisms SSet.{u}).rlp
    (fun _ _ h ↦ SimplexCategory.ext h) (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩)
  exact (MorphismProperty.llp_eq_of_wfs _ _).symm

/-- Reedy の単射左類は合成で閉じる。 -/
lemma comp {X Y Z : CosimplicialObject SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) f)
    (hg : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) g) :
    reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (f ≫ g) := by
  rw [left_eq_llp] at hf hg ⊢
  exact (reedyRight simplex (MorphismProperty.monomorphisms SSet.{u}).rlp).llp.comp_mem _ _ hf hg

/-- Reedy anodyne な射の相対 latching は単射。 -/
lemma of_anodyne {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y)
    (hf : reedyLeft simplex anodyneExtensions f) :
    reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) f :=
  fun j ↦ anodyne_mono _ (hf j)

/-- Reedy anodyne な射の終域も始域とともに Reedy cofibrant。 -/
lemma target {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y)
    (hX : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (initial.to X))
    (hf : reedyLeft simplex anodyneExtensions f) :
    reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (initial.to Y) := by
  have h := comp (initial.to X) f hX (of_anodyne f hf)
  rwa [initial.to_comp] at h

/-- 標準単体の重みは Reedy cofibrant。 -/
lemma standard : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u})
    (initial.to stdSimplex.{u}) := by
  intro j
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
    (BousfieldKanWeightLatching.initialArrowIso stdSimplex j)).mp (StandardSimplexLatching.mono j)

/-- 標準単体の重みの Reedy Kan 置換も Reedy cofibrant。 -/
lemma kanStandard : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u})
    (initial.to (CosimplicialKanReplacement.functor.obj stdSimplex.{u})) :=
  target _ standard (CosimplicialKanReplacement.unit_reedy_anodyne _)

/-- BK 重みの Reedy Kan 置換は Reedy cofibrant。 -/
lemma kanBousfieldKan : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u})
    (initial.to (CosimplicialKanReplacement.functor.obj BousfieldKanWeightLatching.weight.{u})) :=
  target _ BousfieldKanWeightLatching.reedyCofibrant
    (CosimplicialKanReplacement.unit_reedy_anodyne _)

/-- 置換した終頂点比較の二射影の中間図式も Reedy cofibrant。 -/
lemma twoProjections : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u})
    (initial.to (CosimplicialTwoProjections.obj CosimplicialLastVertex.kanWeightMap.{u})) :=
  target _ kanBousfieldKan
    (CosimplicialHornFactorization.factorization.hi
      (CosimplicialTwoProjections.input CosimplicialLastVertex.kanWeightMap))

/-- Reedy cofibrant な終域への全単射 RLP な Reedy 射影には厳密な切断がある。 -/
lemma exists_section {X Y : CosimplicialObject SSet.{u}} (p : X ⟶ Y)
    (hY : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (initial.to Y))
    (hp : reedyRight simplex (MorphismProperty.monomorphisms SSet.{u}).rlp p) :
    ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y := by
  let : ∀ j, HasLiftingProperty (relativeLatchingMap simplex j (initial.to Y))
      (relativeMatchingMap simplex j p) := fun j ↦ hp j _ (hY j)
  let : HasLiftingProperty (initial.to Y) p := Lifting.hasLiftingProperty simplex
  let sq : CommSq (initial.to X) (initial.to Y) p (𝟙 Y) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- 置換した終頂点の二射影分解の target 射影の実際の切断。 -/
def targetSection : CosimplicialKanReplacement.functor.obj stdSimplex.{u} ⟶
    CosimplicialTwoProjections.obj CosimplicialLastVertex.kanWeightMap.{u} :=
  (exists_section _ kanStandard
    CosimplicialLastVertex.kanWeightTargetProjection_matching).choose

/-- 選択した切断と target 射影の合成は厳密な恒等射。 -/
lemma targetSection_projection : targetSection.{u} ≫
    CosimplicialTwoProjections.targetProjection CosimplicialLastVertex.kanWeightMap = 𝟙 _ :=
  (exists_section _ kanStandard
    CosimplicialLastVertex.kanWeightTargetProjection_matching).choose_spec

end
end SerrePositivity.KST.Spectra.ReedyWeightCofibrancy
