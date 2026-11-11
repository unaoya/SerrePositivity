module
public import SerrePositivity.KST.SConstruction.FrameSpanExtension
public import SerrePositivity.KST.SConstruction.FirstRowLowDegrees

/-! # gapped 図式の第一行制限は trivial Kan fibration
概要：任意の第一行の厳密な gapped 延長と全ての相対境界充填を証明する。
方針：零対角の枠の gapped 延長で頂点の全射性を得て、既存の正次元の境界 RLP と合わせる。
規約：C は安定な quasicategory。使われ方：BGT Lemma 7.3 と ∞-S• の加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零対角の図式を枠へ制限すると零対角の枠になる。
方針：枠の対角の区間を (i,i) と同定する。
規約：押し出し性は不要。使われ方：第一行からの零対角補完を入力にする。 -/
lemma zeroFrameVertex_of_zero_diagonal {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C)
    (hz : ∀ i : Fin (n + 1), _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (arObj i i le_rfl)))) :
    IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (frameInclusion n ≫ F)) := by
  intro x hd
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  let a := (nerveEquiv x).val
  have hx : x = ComposableArrows.mk₀ (nerveEquiv x) := (nerveEquiv.symm_apply_apply x).symm
  rw [hx]
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a))
  have ha : a = arObj a.down.val.1 a.down.val.1 le_rfl := by
    apply ULift.ext
    apply Subtype.ext
    exact Prod.ext rfl hd.symm
  rw [ha]
  exact hz _

/-- 概要：任意の第一行は gapped 図式へ厳密に延長できる。
方針：零対角の補完を枠へ制限し、その枠を gapped に延長する。
規約：C は安定な quasicategory。次数零も含む。
使われ方：第一行制限の零次元の境界 RLP。 -/
lemma exists_gapped_with_firstRow (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : firstRowNerve n ⟶ C) :
    ∃ G : arNerve n ⟶ C, IsGapped G ∧ firstRowInclusion n ≫ G = p := by
  obtain ⟨F, hrow, hz⟩ := exists_firstRowDiagramWithZeroDiagonal n C p
  obtain ⟨G, hG, hframe⟩ := exists_gapped_extension_of_zeroFrame (frameInclusion n ≫ F)
    (zeroFrameVertex_of_zero_diagonal F hz)
  refine ⟨G, hG, ?_⟩
  have hi : (firstRowFrameMap n ≫ (framePositiveRow n).ι) ≫ frameInclusion n =
      firstRowInclusion n := by
    simpa only [Category.assoc] using firstRowFrameMap_inclusion.{u} n
  have he := congrArg (fun q => (firstRowFrameMap n ≫ (framePositiveRow n).ι) ≫ q) hframe
  simp only [← Category.assoc, hi] at he
  exact he.trans hrow

/-- 概要：全次数の第一行制限は頂点で全射。
方針：第一行の関手頂点を復号し、gapped 延長を全部分複体の頂点へ戻す。
規約：C は安定な quasicategory。使われ方：零次元の持ち上げ。 -/
lemma firstRowRestriction_vertex_surjective (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    Function.Surjective ((firstRowRestriction n C).app (Opposite.op ⦋0⦌)) := by
  intro d
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (firstRowNerve n) C).symm d
  obtain ⟨G, hG, hrow⟩ := exists_gapped_with_firstRow n C p
  let v : (sConstruction n C) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C G))
    rw [Equiv.symm_apply_apply]
    exact hG⟩
  refine ⟨v, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (firstRowInclusion n ≫ G) = d
  rw [hrow]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply d

/-- 概要：安定な quasicategory の第一行制限は全次数で trivial Kan fibration。
方針：零次元の存在と正次元の相対境界 RLP を合わせる。
規約：追加の存在仮定なし。使われ方：gapped ≃ 第一行と余 fiber の可縮性。 -/
instance firstRowRestriction_trivialKanFibration (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (firstRowRestriction n C) :=
  firstRowRestriction_trivialKanFibration_of_vertexSurjective n C
    (firstRowRestriction_vertex_surjective n C)

/-- 概要：gapped 図式の quasicategory は第一行の関手 quasicategory と同値。
方針：第一行制限の trivial Kan fibration から切断と二つの比較同型を取る。
規約：全 gapped 図式を保ち、選択模型に置き換えない。
使われ方：BGT Lemma 7.3 の同値としての表示。 -/
def firstRowEquivalence (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (sConstruction n C) ((ihom (firstRowNerve n)).obj C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (firstRowRestriction n C)

/-- 概要：第一行を固定した gapped 延長の選択空間は可縮 Kan 複体。
方針：trivial Kan fibration の頂点 fiber の一般定理を使う。
規約：第一行の任意の関手頂点を許す。使われ方：商の coherent な選択の一意性。 -/
lemma firstRowRestriction_vertexFiber_isContractibleKan (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (d : ((ihom (firstRowNerve n)).obj C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (firstRowRestriction n C) d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

end SerrePositivity.KST.SConstruction
