module
public import SerrePositivity.KST.SConstruction.Cofinality.FullyFaithful
public import SerrePositivity.KST.SConstruction.GappedIso
public import SerrePositivity.KST.SConstruction.ObjectSVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.EssentialImageDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FullyFaithfulConeReflection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

/-!
概要：本質像内に値を持つ元の有限 S 図式を、指定された完全射の始域へ戻す。
方針：全図式の持ち上げを正本から取り、充満忠実性で gapped 条件を反映する。
規約：頂点ごとの同型だけで比較せず、同じ Ar 図式全体の関手同型を保持する。
使われ方：D-22 の補対象を有限 S 図式へ適用する際の、像からの回収。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定された充満忠実な完全射は Ar 図式の gapped 条件を反映する。
方針：零対象を同じ完全射の零像と比較し、各四角形は全余錐の反映で戻す。
規約：始域・終域と指定図式を変えない。
使われ方：始域へ戻した有限図式を同じ S_n に含める。 -/
lemma isGapped_of_fullyFaithful_image {n : ℕ} {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val) (F : arNerve n ⟶ X.carrier)
    (hF : IsGapped (F ≫ f.val)) : IsGapped F := by
  constructor
  · intro i
    let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X.carrier
    have hz := f.property.1 z.vertex z.isZero
    have hi := hF.1 i
    let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.zeroVertexIso ⟨_, hz.1, hz.2⟩ ⟨_, hi.1, hi.2⟩
    exact z.isZero.of_vertexIso (hf.preimageVertexIso e)
  · intro i j k l hij hjk hkl
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_fullyFaithful_image f.val hf
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (arSquare i j k l hij hjk hkl ≫ F))
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (arSquare i j k l hij hjk hkl ≫ F ≫ f.val)) ?_).mpr
    · exact hF.2 i j k l hij hjk hkl
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (arSquare i j k l hij hjk hkl ≫ F)) ≫ f.val = _
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone]

/-- 概要：本質像内の gapped 図式を元の始域の S_n 頂点として全図式同型まで回収する。
方針：全 Ar 図式の持ち上げと gapped 条件の反映を合成する。
規約：各辺や面を個別に選び直さない。
使われ方：補対象で本質像へ入れた有限 S 図式の同時回収。 -/
lemma exists_sVertex_of_pointwise_image {n : ℕ} {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val) (F : arNerve n ⟶ Y.carrier)
    (hF : IsGapped F)
    (himage : ∀ a : (arNerve n) _⦋0⦌, ∃ x : X.carrier _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.val.app (Opposite.op ⦋0⦌) x)
        (F.app (Opposite.op ⦋0⦌) a))) :
    ∃ x : (sConstruction n X.carrier) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (gappedDiagram x ≫ f.val) F) := by
  obtain ⟨G, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.exists_diagram_in_fullyFaithful_source f.val hf F himage
  have hG := isGapped_of_fullyFaithful_image f hf G (hF.of_functorIso e.symm)
  refine ⟨gappedObjectVertex G hG, ?_⟩
  rw [gappedDiagram_gappedObjectVertex]
  exact ⟨e⟩

/-- 概要：像内の各 Ar 値から、元の S_n 射の本質像への所属を回収する。
方針：全図式同型を gapped 包含の充満忠実性で同じ S_n の頂点同型へ反映する。
規約：図式の像の同型を成分ごとの同型へ弱めない。
使われ方：パラメータ付き有限 S 図式の全族持ち上げ。 -/
lemma exists_sVertexIso_of_pointwise_image {n : ℕ} {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val) (y : (sConstruction n Y.carrier) _⦋0⦌)
    (himage : ∀ a : (arNerve n) _⦋0⦌, ∃ x : X.carrier _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.val.app (Opposite.op ⦋0⦌) x)
        ((gappedDiagram y).app (Opposite.op ⦋0⦌) a))) :
    ∃ x : (sConstruction n X.carrier) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (((sEndofunctor n).map f).val.app (Opposite.op ⦋0⦌) x) y) := by
  obtain ⟨x, ⟨e⟩⟩ := exists_sVertex_of_pointwise_image f hf (gappedDiagram y)
    (gappedDiagram_isGapped y) himage
  refine ⟨x, ⟨?_⟩⟩
  let : Quasicategory (diagramSpace n Y.carrier) := by
    dsimp [diagramSpace]
    infer_instance
  let : Quasicategory (gappedSubcomplex n Y.carrier).toSSet :=
    sConstruction_quasicategory n Y.carrier
  have hι : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (gappedSubcomplex n Y.carrier).ι :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  apply hι.preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((((sEndofunctor n).map f).val.app (Opposite.op ⦋0⦌) x).val) y.val
  have hx := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) Y.carrier).apply_symm_apply
    ((((sEndofunctor n).map f).val.app (Opposite.op ⦋0⦌) x).val)
  have hy := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) Y.carrier).apply_symm_apply y.val
  rw [← hx, ← hy]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (gappedDiagram (((sEndofunctor n).map f).val.app (Opposite.op ⦋0⦌) x)) (gappedDiagram y)
  exact (gappedDiagram_sPostcompCofiber f.val f.property x).symm ▸ e

/-- 概要：全ての Ar 値が本質像内にあるパラメータ付き S_n 図式を全族で始域へ戻す。
方針：各 S_n 頂点の像所属と同じ S_n 射の充満忠実性を全図式持ち上げに渡す。
規約：パラメータの quasicategory 性を要求せず、全高次単体を関手同型で比較する。
使われ方：補対象を足した有限 S 図式の面・退化を含む同時回収。 -/
lemma exists_sFamily_of_pointwise_image {n : ℕ} {K : SSet.{u}} {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val) (F : K ⟶ sConstruction n Y.carrier)
    (himage : ∀ k : K _⦋0⦌, ∀ a : (arNerve n) _⦋0⦌, ∃ x : X.carrier _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.val.app (Opposite.op ⦋0⦌) x)
        ((gappedDiagram (F.app (Opposite.op ⦋0⦌) k)).app (Opposite.op ⦋0⦌) a))) :
    ∃ G : K ⟶ sConstruction n X.carrier,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ ((sEndofunctor n).map f).val) F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.exists_diagram_in_fullyFaithful_source ((sEndofunctor n).map f).val
    (sEndofunctor_map_isFullyFaithful n f hf) F
    (fun k => exists_sVertexIso_of_pointwise_image f hf _ (himage k))

end SerrePositivity.KST.SConstruction.Cofinality
